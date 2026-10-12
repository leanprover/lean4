// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: public import Lean.Exception
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "postpone"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 147, 226, 184, 25, 148, 1, 197)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_postponeExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unsupportedSyntax"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 51, 203, 242, 163, 164, 191, 80)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "abortCommandElab"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 77, 82, 173, 197, 44, 118, 60)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortCommandExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "abortTermElab"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 148, 87, 84, 76, 250, 173, 131)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTermExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "abortTactic"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 196, 8, 94, 141, 48, 206, 206)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTacticExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "autoBoundImplicit"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 126, 94, 243, 65, 39, 77, 227)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_autoBoundImplicitExceptionId;
static lean_once_cell_t l_Lean_Elab_throwPostpone___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwPostpone___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ill-formed syntax"};
static const lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "localId"};
static const lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 23, 246, 250, 79, 174, 148, 42)}};
static const lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "a universe level named `"};
static const lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1;
static const lean_string_object l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortException___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_mkMessageCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_mkMessageCore___closed__0 = (const lean_object*)&l_Lean_Elab_mkMessageCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_));
v___x_6_ = l_Lean_registerInternalExceptionId(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
return v_res_9_;
}
}
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_));
v___x_15_ = l_Lean_registerInternalExceptionId(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
return v_res_18_;
}
}
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_));
v___x_24_ = l_Lean_registerInternalExceptionId(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_25_;
v_res_25_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
return v_res_27_;
}
}
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_));
v___x_33_ = l_Lean_registerInternalExceptionId(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
return v_res_36_;
}
}
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_));
v___x_42_ = l_Lean_registerInternalExceptionId(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_43_;
v_res_43_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
return v_res_45_;
}
}
lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_));
v___x_51_ = l_Lean_registerInternalExceptionId(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_52_;
v_res_52_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Elab_throwPostpone___redArg___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_Elab_postponeExceptionId;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object* v_inst_58_){
_start:
{
lean_object* v_throw_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_throw_59_ = lean_ctor_get(v_inst_58_, 0);
lean_inc(v_throw_59_);
lean_dec_ref(v_inst_58_);
v___x_60_ = lean_obj_once(&l_Lean_Elab_throwPostpone___redArg___closed__0, &l_Lean_Elab_throwPostpone___redArg___closed__0_once, _init_l_Lean_Elab_throwPostpone___redArg___closed__0);
v___x_61_ = lean_apply_2(v_throw_59_, lean_box(0), v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object* v_m_62_, lean_object* v_00_u03b1_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Elab_throwPostpone___redArg(v_inst_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_box(0);
v___x_67_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object* v_inst_69_){
_start:
{
lean_object* v_throw_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_throw_70_ = lean_ctor_get(v_inst_69_, 0);
lean_inc(v_throw_70_);
lean_dec_ref(v_inst_69_);
v___x_71_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0);
v___x_72_ = lean_apply_2(v_throw_70_, lean_box(0), v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object* v_m_73_, lean_object* v_00_u03b1_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_inst_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0));
v___x_79_ = l_Lean_stringToMessageData(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1);
v___x_83_ = l_Lean_throwError___redArg(v_inst_80_, v_inst_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object* v_m_84_, lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Elab_throwIllFormedSyntax___redArg(v_inst_86_, v_inst_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object* v_inst_92_, lean_object* v_n_93_){
_start:
{
lean_object* v_throw_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_107_; 
v_throw_94_ = lean_ctor_get(v_inst_92_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_inst_92_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_inst_92_, 1);
lean_dec(v_unused_108_);
v___x_96_ = v_inst_92_;
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_throw_94_);
lean_dec(v_inst_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_98_ = l_Lean_Elab_autoBoundImplicitExceptionId;
v___x_99_ = l_Lean_KVMap_empty;
v___x_100_ = ((lean_object*)(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1));
v___x_101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_101_, 0, v_n_93_);
v___x_102_ = l_Lean_KVMap_insert(v___x_99_, v___x_100_, v___x_101_);
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 1);
lean_ctor_set(v___x_96_, 1, v___x_102_);
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_104_ = v___x_96_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_apply_2(v_throw_94_, lean_box(0), v___x_104_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object* v_m_109_, lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_n_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(v_inst_111_, v_n_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object* v_ex_117_){
_start:
{
if (lean_obj_tag(v_ex_117_) == 1)
{
lean_object* v_id_118_; lean_object* v_extra_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_id_118_ = lean_ctor_get(v_ex_117_, 0);
v_extra_119_ = lean_ctor_get(v_ex_117_, 1);
v___x_120_ = l_Lean_Elab_autoBoundImplicitExceptionId;
v___x_121_ = l_Lean_instBEqInternalExceptionId_beq(v_id_118_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1));
v___x_124_ = ((lean_object*)(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1));
v___x_125_ = l_Lean_KVMap_getName(v_extra_119_, v___x_123_, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object* v_ex_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(v_ex_128_);
lean_dec_ref(v_ex_128_);
return v_res_129_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0));
v___x_132_ = l_Lean_stringToMessageData(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2));
v___x_135_ = l_Lean_stringToMessageData(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_u_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1);
v___x_140_ = l_Lean_MessageData_ofName(v_u_138_);
v___x_141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3);
v___x_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = l_Lean_throwError___redArg(v_inst_136_, v_inst_137_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object* v_m_145_, lean_object* v_00_u03b1_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_u_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(v_inst_147_, v_inst_148_, v_u_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_box(0);
v___x_152_ = l_Lean_Elab_abortCommandExceptionId;
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object* v_inst_154_){
_start:
{
lean_object* v_throw_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_throw_155_ = lean_ctor_get(v_inst_154_, 0);
lean_inc(v_throw_155_);
lean_dec_ref(v_inst_154_);
v___x_156_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0);
v___x_157_ = lean_apply_2(v_throw_155_, lean_box(0), v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object* v_00_u03b1_158_, lean_object* v_m_159_, lean_object* v_inst_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Elab_throwAbortCommand___redArg(v_inst_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = l_Lean_Elab_abortTermExceptionId;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object* v_inst_165_){
_start:
{
lean_object* v_throw_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_throw_166_ = lean_ctor_get(v_inst_165_, 0);
lean_inc(v_throw_166_);
lean_dec_ref(v_inst_165_);
v___x_167_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0);
v___x_168_ = lean_apply_2(v_throw_166_, lean_box(0), v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object* v_00_u03b1_169_, lean_object* v_m_170_, lean_object* v_inst_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Elab_throwAbortTerm___redArg(v_inst_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
v___x_174_ = l_Lean_Elab_abortTacticExceptionId;
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object* v_inst_176_){
_start:
{
lean_object* v_throw_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_throw_177_ = lean_ctor_get(v_inst_176_, 0);
lean_inc(v_throw_177_);
lean_dec_ref(v_inst_176_);
v___x_178_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0);
v___x_179_ = lean_apply_2(v_throw_177_, lean_box(0), v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object* v_00_u03b1_180_, lean_object* v_m_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Elab_throwAbortTactic___redArg(v_inst_182_);
return v___x_183_;
}
}
uint8_t l_Lean_Elab_isAbortTacticException(lean_object* v_ex_184_){
_start:
{
if (lean_obj_tag(v_ex_184_) == 1)
{
lean_object* v_id_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_id_185_ = lean_ctor_get(v_ex_184_, 0);
v___x_186_ = l_Lean_Elab_abortTacticExceptionId;
v___x_187_ = l_Lean_instBEqInternalExceptionId_beq(v_id_185_, v___x_186_);
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isAbortTacticException_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_184_ = stack[0].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Lean_Elab_isAbortTacticException(v_ex_184_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object* v_ex_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Elab_isAbortTacticException(v_ex_190_);
lean_dec_ref(v_ex_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object* v_id_193_){
_start:
{
uint8_t v___y_195_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = l_Lean_Elab_abortCommandExceptionId;
v___x_199_ = l_Lean_instBEqInternalExceptionId_beq(v_id_193_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = l_Lean_Elab_abortTermExceptionId;
v___x_201_ = l_Lean_instBEqInternalExceptionId_beq(v_id_193_, v___x_200_);
v___y_195_ = v___x_201_;
goto v___jp_194_;
}
else
{
v___y_195_ = v___x_199_;
goto v___jp_194_;
}
v___jp_194_:
{
if (v___y_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = l_Lean_Elab_abortTacticExceptionId;
v___x_197_ = l_Lean_instBEqInternalExceptionId_beq(v_id_193_, v___x_196_);
return v___x_197_;
}
else
{
return v___y_195_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_isAbortExceptionId_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_193_ = stack[0].m_obj;
uint8_t v_res_202_;
v_res_202_ = l_Lean_Elab_isAbortExceptionId(v_id_193_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object* v_id_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lean_Elab_isAbortExceptionId(v_id_203_);
lean_dec(v_id_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
uint8_t l_Lean_Elab_isAbortException(lean_object* v_ex_206_){
_start:
{
if (lean_obj_tag(v_ex_206_) == 1)
{
lean_object* v_id_207_; uint8_t v___x_208_; 
v_id_207_ = lean_ctor_get(v_ex_206_, 0);
v___x_208_ = l_Lean_Elab_isAbortExceptionId(v_id_207_);
return v___x_208_;
}
else
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_isAbortException_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_206_ = stack[0].m_obj;
uint8_t v_res_210_;
v_res_210_ = l_Lean_Elab_isAbortException(v_ex_206_);
stack->m_num = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortException___boxed(lean_object* v_ex_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_Elab_isAbortException(v_ex_211_);
lean_dec_ref(v_ex_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
lean_object* l_Lean_Elab_mkMessageCore(lean_object* v_fileName_215_, lean_object* v_fileMap_216_, lean_object* v_data_217_, uint8_t v_severity_218_, lean_object* v_pos_219_, lean_object* v_endPos_220_){
_start:
{
lean_object* v_pos_221_; lean_object* v_endPos_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_inc_ref(v_fileMap_216_);
v_pos_221_ = l_Lean_FileMap_toPosition(v_fileMap_216_, v_pos_219_);
v_endPos_222_ = l_Lean_FileMap_toPosition(v_fileMap_216_, v_endPos_220_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_endPos_222_);
v___x_224_ = 0;
v___x_225_ = ((lean_object*)(l_Lean_Elab_mkMessageCore___closed__0));
v___x_226_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_226_, 0, v_fileName_215_);
lean_ctor_set(v___x_226_, 1, v_pos_221_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
lean_ctor_set(v___x_226_, 3, v___x_225_);
lean_ctor_set(v___x_226_, 4, v_data_217_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5 + 1, v_severity_218_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5 + 2, v___x_224_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_Elab_mkMessageCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileName_215_ = stack[0].m_obj;
lean_object* v_fileMap_216_ = stack[1].m_obj;
lean_object* v_data_217_ = stack[2].m_obj;
uint8_t v_severity_218_ = stack[3].m_num;
lean_object* v_pos_219_ = stack[4].m_obj;
lean_object* v_endPos_220_ = stack[5].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_Elab_mkMessageCore(v_fileName_215_, v_fileMap_216_, v_data_217_, v_severity_218_, v_pos_219_, v_endPos_220_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* v_fileName_228_, lean_object* v_fileMap_229_, lean_object* v_data_230_, lean_object* v_severity_231_, lean_object* v_pos_232_, lean_object* v_endPos_233_){
_start:
{
uint8_t v_severity_boxed_234_; lean_object* v_res_235_; 
v_severity_boxed_234_ = lean_unbox(v_severity_231_);
v_res_235_ = l_Lean_Elab_mkMessageCore(v_fileName_228_, v_fileMap_229_, v_data_230_, v_severity_boxed_234_, v_pos_232_, v_endPos_233_);
lean_dec(v_endPos_233_);
lean_dec(v_pos_232_);
return v_res_235_;
}
}
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_postponeExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_unsupportedSyntaxExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortCommandExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTermExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTacticExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoBoundImplicitExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Exception(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Exception(builtin);
}
#ifdef __cplusplus
}
#endif
