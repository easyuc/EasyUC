type EFI_GUID = [
  | gEfiGlobalVariableGuid
  | gEfiVT100PlusGuid
  | gEfiVT100Guid
  | gEfiPcAnsiGuid
  | gEfiVTUTF8Guid
  | gEfiUartDevicePathGuid
  | gEfiSasDevicePathGuid
  | gEfiPartTypeLegacyMbrGuid
  | gEfiPartTypeSystemPartGuid
  | gEfiPartTypeUnusedGuid
  | gEfiDebugImageInfoTableGuid
  | gEfiAcpiTableGuid
  | gEfiAcpi20TableGuid
  | gEfiAcpi10TableGuid
  | gEfiSmbiosTableGuid
  | gEfiMpsTableGuid
  | gEfiAuthenticationChapLocalGuid
  | gEfiAuthenticationChapRadiusGuid
  | gEfiFileSystemVolumeLabelInfoIdGuid
  | gEfiFileSystemInfoGuid
  | gEfiFileInfoGuid
  | gBootObjectAuthorizationParmsetGuid
  | gEfiPlatformToDriverConfigurationClpGuid
  | gEfiHiiKeyBoardLayoutGuid
  | gEfiHashAlgorithmMD5Guid
  | gEfiHashAlgorithmSha512Guid
  | gEfiHashAlgorithmSha384Guid
  | gEfiHashAlgorithmSha256Guid
  | gEfiHashAlgorithmSha224Guid
  | gEfiHashAlgorithmSha1Guid
  | gEfiEventReadyToBootGuid
  | gEfiEventMemoryMapChangeGuid
  | gEfiEventVirtualAddressChangeGuid
  | gEfiEventExitBootServicesGuid
  | gEfiDebugPortVariableGuid
  | gEfiDebugPortDevicePathGuid
  | gEfiHiiPlatformSetupFormsetGuid
  | gEfiHiiDriverHealthFormsetGuid
  | gEfiHiiUserCredentialFormsetGuid
  | gEfiHiiStandardFormGuid
  | gEfiMemoryOverwriteControlDataGuid
  | gEfiMemoryOverwriteRequestControlLockGuid
  | gEfiCertTypeRsa2048Sha256Guid
  | gEfiEventNotificationTypeCmcGuid
  | gEfiEventNotificationTypeCpeGuid
  | gEfiEventNotificationTypeMceGuid
  | gEfiEventNotificationTypePcieGuid
  | gEfiEventNotificationTypeInitGuid
  | gEfiEventNotificationTypeNmiGuid
  | gEfiEventNotificationTypeBootGuid
  | gEfiEventNotificationTypeDmarGuid
  | gEfiEventNotificationTypeSeaGuid
  | gEfiEventNotificationTypeSeiGuid
  | gEfiEventNotificationTypePeiGuid
  | gEfiProcessorGenericErrorSectionGuid
  | gEfiProcessorSpecificErrorSectionGuid
  | gEfiIa32X64ProcessorErrorSectionGuid
  | gEfiPlatformMemoryErrorSectionGuid
  | gEfiPcieErrorSectionGuid
  | gEfiFirmwareErrorSectionGuid
  | gEfiPciBusErrorSectionGuid
  | gEfiPciDevErrorSectionGuid
  | gEfiDMArGenericErrorSectionGuid
  | gEfiDirectedIoDMArErrorSectionGuid
  | gEfiIommuDMArErrorSectionGuid
  | gEfiEventUserProfileChangedGuid
  | gEfiUserCredentialClassUnknownGuid
  | gEfiUserCredentialClassPasswordGuid
  | gEfiUserCredentialClassSmartCardGuid
  | gEfiUserCredentialClassFingerprintGuid
  | gEfiUserCredentialClassHandprintGuid
  | gEfiUserCredentialClassSecureCardGuid
  | gEfiUserInfoAccessSetupAdminGuid
  | gEfiUserInfoAccessSetupNormalGuid
  | gEfiUserInfoAccessSetupRestrictedGuid
  | gEfiImageSecurityDatabaseGuid
  | gEfiCertSha256Guid
  | gEfiCertRsa2048Guid
  | gEfiCertRsa2048Sha256Guid
  | gEfiCertSha1Guid
  | gEfiCertRsa2048Sha1Guid
  | gEfiCertX509Guid
  | gEfiKmsFormatGeneric128Guid
  | gEfiKmsFormatGeneric160Guid
  | gEfiKmsFormatGeneric256Guid
  | gEfiKmsFormatGeneric512Guid
  | gEfiKmsFormatGeneric1024Guid
  | gEfiKmsFormatGeneric2048Guid
  | gEfiKmsFormatGeneric3072Guid
  | gEfiKmsFormatMd2128Guid
  | gEfiKmsFormatMdc2128Guid
  | gEfiKmsFormatMd4128Guid
  | gEfiKmsFormatMdc4128Guid
  | gEfiKmsFormatMd5128Guid
  | gEfiKmsFormatMd5sha128Guid
  | gEfiKmsFormatSha1160Guid
  | gEfiKmsFormatSha256256Guid
  | gEfiKmsFormatSha512512Guid
  | gEfiKmsFormatAesxts128Guid
  | gEfiKmsFormatAesxts256Guid
  | gEfiKmsFormatAescbc128Guid
  | gEfiKmsFormatAescbc256Guid
  | gEfiKmsFormatRsasha11024Guid
  | gEfiKmsFormatRsasha12048Guid
  | gEfiKmsFormatRsasha2562048Guid
  | gEfiKmsFormatRsasha2563072Guid
  | gEfiCertSha224Guid
  | gEfiCertSha384Guid
  | gEfiCertSha512Guid
  | gEfiCertPkcs7Guid
  | gEfiHashAlgorithmSha1NoPadGuid
  | gEfiHashAlgorithmSha256NoPadGuid
  | gEfiFmpCapsuleGuid
  | gEfiCertX509Sha256Guid
  | gEfiCertX509Sha384Guid
  | gEfiCertX509Sha512Guid
  | gEfiRngAlgorithmSp80090Hash256Guid
  | gEfiRngAlgorithmSp80090Hmac256Guid
  | gEfiRngAlgorithmSp80090Ctr256Guid
  | gEfiRngAlgorithmX9313DesGuid
  | gEfiRngAlgorithmX931AesGuid
  | gEfiRngAlgorithmRawGuid (* "Guid" appended to name *)
  | gEfiAdapterInfoMediaStateGuid
  | gEfiAdapterInfoNetworkBootGuid
  | gEfiAdapterInfoSanMacAddressGuid
  | gEfiCapsuleReportGuid
  | gEfiSystemResourceTableGuid
  | gEfiAdapterInfoUndiIpv6SupportGuid
  | gEfiRegexSyntaxTypePosixExtendedGuid
  | gEfiRegexSyntaxTypeEcma262Guid
  | gEfiRegexSyntaxTypePerlGuid
  | gEfiPlatformMemory2ErrorSectionGuid
  | gEfiBlockIoCryptoAlgoAesXtsGuid
  | gEfiBlockIoCryptoAlgoAesCbcMsBitlockerGuid
  | gEfiPaddingRsassaPkcs1V1P5Guid
  | gEfiPaddingRsassaPssGuid
  | gEfiPaddingNoneGuid
  | gEfiPaddingRsaesPkcs1V1P5Guid
  | gEfiPaddingRsaesOaepGuid
  | gEfiSmbios3TableGuid
  | gEfiBootManagerPolicyConsoleGuid
  | gEfiBootManagerPolicyNetworkGuid
  | gEfiBootManagerPolicyConnectAllGuid
  | gEfiVirtualDiskGuid
  | gEfiVirtualCdGuid
  | gEfiPersistentVirtualDiskGuid
  | gEfiPersistentVirtualCdGuid
  | gEfiMemoryAttributesTableGuid
  | gEfiArmProcessorErrorSectionGuid
  | gEfiHiiImageDecoderNameJpegGuid
  | gEfiHiiImageDecoderNamePngGuid
  | gEfiBttAbstractionGuid
  | gEfiJsonConfigDataTableGuid
  | gEfiJsonCapsuleDataTableGuid
  | gEfiJsonCapsuleResultTableGuid
  | gEfiJsonCapsuleIdGuid
  | gEfiHiiRestStyleFormsetGuid
  | gEfiRtPropertiesTableGuid
  | gEfiSerialTerminalDeviceTypeGuid
  | gPeiAprioriFileNameGuid
  | gAprioriGuid
  | gEfiFirmwareFileSystem2Guid
  | gEfiFirmwareVolumeTopFileGuid
  | gEfiHobMemoryAllocModuleGuid
  | gEfiHobMemoryAllocStackGuid
  | gEfiHobMemoryAllocBspStoreGuid
  | gEfiEventLegacyBootGuid
  | gEfiHobListGuid
  | gEfiDxeServicesTableGuid
  | gEfiMdePkgTokenSpaceGuid
  | gEfiHardwareErrorVariableGuid
  | gEfiEventDxeDispatchGuid
  | gEfiDiskInfoIdeInterfaceGuid
  | gEfiDiskInfoScsiInterfaceGuid
  | gEfiDiskInfoUsbInterfaceGuid
  | gEfiDiskInfoAhciInterfaceGuid
  | gEfiStatusCodeDataTypeStringGuid
  | gEfiStatusCodeSpecificDataGuid
  | gEfiFirmwareFileSystem3Guid
  | gEfiEndOfDxeEventGroupGuid
  | gEfiFirmwareContentsSignedGuid
  | gEfiVectorHandoffTableGuid
  | gAdapterInfoPlatformSecurityGuid
  | gEfiDiskInfoNvmeInterfaceGuid
  | gEfiGraphicsInfoHobGuid
  | gEfiDiskInfoUfsInterfaceGuid
  | gEfiGraphicsDeviceInfoHobGuid
  | gEfiSmmSmramMemoryGuid
  | gEfiDiskInfoSdMmcInterfaceGuid
  | gWindowsUxCapsuleGuid
  | gTianoCustomDecompressGuid
  | gLinuxEfiInitrdMediaGuid
  | gEfiCcFinalEventsTableGuid
  | gEfiIa32X64ErrorTypeCacheCheckGuid
  | gEfiIa32X64ErrorTypeTlbCheckGuid
  | gEfiIa32X64ErrorTypeBusCheckGuid
  | gEfiIa32X64ErrorTypeMsCheckGuid
  | gEfiPeiMasterBootModePpiGuid

  (* Include/Ppi/DxeIpl.h *)
  | gEfiDxeIplPpiGuid

  (* Include/Ppi/MemoryDiscovered.h *)
  | gEfiPeiMemoryDiscoveredPpiGuid

  (* Include/Ppi/BootInRecoveryMode.h *)
  | gEfiPeiBootInRecoveryModePpiGuid

  (* Include/Ppi/EndOfPeiPhase.h *)
  | gEfiEndOfPeiSignalPpiGuid

  (* Include/Ppi/Reset.h *)
  | gEfiPeiResetPpiGuid

  (* Include/Ppi/StatusCode.h *)
  | gEfiPeiStatusCodePpiGuid

  (* Include/Ppi/Security2.h *)
  | gEfiPeiSecurity2PpiGuid

  (* Include/Ppi/TemporaryRamSupport.h *)
  | gEfiTemporaryRamSupportPpiGuid

  (* Include/Ppi/CpuIo.h *)
  | gEfiPeiCpuIoPpiInstalledGuid

  (* Include/Ppi/PciCfg2.h *)
  | gEfiPciCfg2PpiGuid

  (* Include/Ppi/Stall.h *)
  | gEfiPeiStallPpiGuid

  (* Include/Ppi/ReadOnlyVariable2.h *)
  | gEfiPeiReadOnlyVariable2PpiGuid

  (* Include/Ppi/SecPlatformInformation.h *)
  | gEfiSecPlatformInformationPpiGuid

  (* Include/Ppi/LoadImage.h *)
  | gEfiPeiLoadedImagePpiGuid

  (* Include/Ppi/Smbus2.h *)
  | gEfiPeiSmbus2PpiGuid

  (* Include/Ppi/FirmwareVolumeInfo.h *)
  | gEfiPeiFirmwareVolumeInfoPpiGuid

  (* Include/Ppi/LoadFile.h *)
  | gEfiPeiLoadFilePpiGuid

  (* Include/Ppi/Decompress.h *)
  | gEfiPeiDecompressPpiGuid

  (* Include/Ppi/Pcd.h *)
  | gPcdPpiGuid

  (* Include/Ppi/PcdInfo.h *)
  | gGetPcdInfoPpiGuid

  (*
   * PPIs defined in PI 1.2.
   *)

  (* Include/Ppi/RecoveryModule.h *)
  | gEfiPeiRecoveryModulePpiGuid

  (* Include/Ppi/DeviceRecoveryModule.h *)
  | gEfiPeiDeviceRecoveryModulePpiGuid

  (* Include/Ppi/BlockIo.h *)
  | gEfiPeiVirtualBlockIoPpiGuid

  (* Include/Ppi/S3Resume2.h *)
  | gEfiPeiS3Resume2PpiGuid

  (* Include/Ppi/ReportStatusCodeHandler.h *)
  | gEfiPeiRscHandlerPpiGuid

  (* Include/Ppi/PiPcd.h *)
  | gEfiPeiPcdPpiGuid

  (*
   * PPIs defined in PI 1.2.1.
   *)

  (* Include/Ppi/PiPcdInfo.h *)
  | gEfiGetPcdInfoPpiGuid

  (* Include/Ppi/TemporaryRamDone.h *)
  | gEfiTemporaryRamDonePpiGuid

  (* Include/Ppi/VectorHandoffInfo.h *)
  | gEfiVectorHandoffInfoPpiGuid

  (* Include/Ppi/IsaHc.h *)
  | gEfiIsaHcPpiGuid

  (* Include/Ppi/SuperIo.h *)
  | gEfiSioPpiGuid

  (*
   * PPIs defined in PI 1.3.
   *)

  (* Include/Ppi/I2cMaster.h *)
  | gEfiPeiI2cMasterPpiGuid

  (* Include/Ppi/FirmwareVolumeInfo2.h *)
  | gEfiPeiFirmwareVolumeInfo2PpiGuid

  (*
   * PPIs defined in PI 1.4.
   *)

  (* Include/Ppi/Graphics.h *)
  | gEfiPeiGraphicsPpiGuid

  (* Include/Ppi/MpServices.h *)
  | gEfiPeiMpServicesPpiGuid

  (* Include/Ppi/Capsule.h *)
  | gEfiPeiCapsulePpiGuid
  | gPeiCapsulePpiGuid

  (* Include/Ppi/Reset2.h *)
  | gEfiPeiReset2PpiGuid

  (* Include/Ppi/BlockIo2.h *)
  | gEfiPeiVirtualBlockIo2PpiGuid

  (* Include/Ppi/SecPlatformInformation.h *)
  | gEfiSecPlatformInformation2PpiGuid

  (*
   * PPIs defined in PI 1.5.
   *)

  (* Include/Ppi/SecHobData.h *)
  | gEfiSecHobDataPpiGuid

  (* Include/Ppi/MmAccess.h *)
  | gEfiPeiMmAccessPpiGuid

  (* Include/Ppi/MmControl.h *)
  | gEfiPeiMmControlPpiGuid

  (* Include/Ppi/MmConfiguration.h *)
  | gEfiPeiMmConfigurationPpiGuid  (* "Guid" appended to name *)

  (* Include/Ppi/MmCommunication.h *)
  | gEfiPeiMmCommunicationPpiGuid

  (*
   * PPIs defined in PI 1.7.
   *)

  (* Include/Ppi/PeiCoreFvLocation.h *)
  | gEfiPeiCoreFvLocationPpiGuid

  (* Include/Ppi/DelayedDispatch.h *)
  | gEfiPeiDelayedDispatchPpiGuid

(* [Protocols] ------------------------------------------------------*)
  (* Include/Protocol/Pcd.h *)
  | gPcdProtocolGuid

  (* Include/Protocol/PcdInfo.h *)
  | gGetPcdInfoProtocolGuid

  (* Include/Protocol/CcMeasurement.h *)
  | gEfiCcMeasurementProtocolGuid

  (*
   * Protocols defined in PI1.0.
   *)

  (* Include/Protocol/Bds.h *)
  | gEfiBdsArchProtocolGuid

  (* Include/Protocol/Cpu.h *)
  | gEfiCpuArchProtocolGuid

  (* Include/Protocol/Metronome.h *)
  | gEfiMetronomeArchProtocolGuid

  (* Include/Protocol/MonotonicCounter.h *)
  | gEfiMonotonicCounterArchProtocolGuid

  (* Include/Protocol/RealTimeClock.h *)
  | gEfiRealTimeClockArchProtocolGuid

  (* Include/Protocol/Reset.h *)
  | gEfiResetArchProtocolGuid

  (* Include/Protocol/Runtime.h *)
  | gEfiRuntimeArchProtocolGuid

  (* Include/Protocol/Security.h *)
  | gEfiSecurityArchProtocolGuid

  (* Include/Protocol/SecurityPolicy.h *)
  | gEfiSecurityPolicyProtocolGuid

  (* Include/Protocol/Timer.h *)
  | gEfiTimerArchProtocolGuid

  (* Include/Protocol/VariableWrite.h *)
  | gEfiVariableWriteArchProtocolGuid

  (* Include/Protocol/Variable.h *)
  | gEfiVariableArchProtocolGuid

  (* Include/Protocol/WatchdogTimer.h *)
  | gEfiWatchdogTimerArchProtocolGuid

  (* Include/Protocol/StatusCode.h *)
  | gEfiStatusCodeRuntimeProtocolGuid

  (* Include/Protocol/SmbusHc.h *)
  | gEfiSmbusHcProtocolGuid

  (* Include/Protocol/FirmwareVolume2.h *)
  | gEfiFirmwareVolume2ProtocolGuid

  (* Include/Protocol/FirmwareVolumeBlock.h *)
  | gEfiFirmwareVolumeBlockProtocolGuid

  (* Include/Protocol/Capsule.h *)
  | gEfiCapsuleArchProtocolGuid

  (*
   * Protocols defined in PI 1.2.
   *)

  (* Include/Protocol/MpService.h *)
  | gEfiMpServiceProtocolGuid

  (* Include/Protocol/PciHostBridgeResourceAllocation.h *)
  | gEfiPciHostBridgeResourceAllocationProtocolGuid

  (* Include/Protocol/PciPlatform.h *)
  | gEfiPciPlatformProtocolGuid

  (* Include/Protocol/PciOverride.h *)
  | gEfiPciOverrideProtocolGuid

  (* Include/Protocol/PciEnumerationComplete.h *)
  | gEfiPciEnumerationCompleteProtocolGuid

  (* Include/Protocol/IncompatiblePciDeviceSupport.h *)
  | gEfiIncompatiblePciDeviceSupportProtocolGuid

  (* Include/Protocol/PciHotPlugInit.h *)
  | gEfiPciHotPlugInitProtocolGuid

  (* Include/Protocol/PciHotPlugRequest.h *)
  | gEfiPciHotPlugRequestProtocolGuid

  (* Include/Protocol/IdeControllerInit.h *)
  | gEfiIdeControllerInitProtocolGuid

  (* Include/Protocol/DiskInfo.h *)
  | gEfiDiskInfoProtocolGuid

  (* Include/Protocol/Smbios.h *)
  | gEfiSmbiosProtocolGuid

  (* Include/Protocol/S3SaveState.h *)
  | gEfiS3SaveStateProtocolGuid

  (* Include/Protocol/S3SmmSaveState.h *)
  | gEfiS3SmmSaveStateProtocolGuid

  (* Include/Protocol/ReportStatusCodeHandler.h *)
  | gEfiRscHandlerProtocolGuid

  (* Include/Protocol/SmmReportStatusCodeHandler.h *)
  | gEfiSmmRscHandlerProtocolGuid

  (* Include/Protocol/AcpiSystemDescriptionTable.h *)
  | gEfiAcpiSdtProtocolGuid

  (* Include/Protocol/SuperIo.h *)
  | gEfiSioProtocolGuid

  (* Include/Protocol/SmmCpuIo2.h *)
  | gEfiSmmCpuIo2ProtocolGuid

  (* Include/Protocol/SmmBase2.h *)
  | gEfiSmmBase2ProtocolGuid

  (* Include/Protocol/SmmAccess2.h *)
  | gEfiSmmAccess2ProtocolGuid

  (* Include/Protocol/SmmControl2.h *)
  | gEfiSmmControl2ProtocolGuid

  (* Include/Protocol/SmmConfiguration.h *)
  | gEfiSmmConfigurationProtocolGuid

  (* Include/Protocol/SmmReadyToLock.h *)
  | gEfiSmmReadyToLockProtocolGuid

  (* Include/Protocol/DxeSmmReadyToLock.h *)
  | gEfiDxeSmmReadyToLockProtocolGuid

  (* Include/Protocol/SmmCommunication.h *)
  | gEfiSmmCommunicationProtocolGuid

  (* Include/Protocol/SmmStatusCode.h *)
  | gEfiSmmStatusCodeProtocolGuid

  (* Include/Protocol/SmmCpu.h *)
  | gEfiSmmCpuProtocolGuid

  (* Include/Protocol/SmmPciRootBridgeIo.h *)
  | gEfiSmmPciRootBridgeIoProtocolGuid

  (* Include/Protocol/SmmSwDispatch2.h *)
  | gEfiSmmSwDispatch2ProtocolGuid

  (* Include/Protocol/SmmSxDispatch2.h *)
  | gEfiSmmSxDispatch2ProtocolGuid

  (* Include/Protocol/SmmPeriodicTimerDispatch2.h *)
  | gEfiSmmPeriodicTimerDispatch2ProtocolGuid

  (* Include/Protocol/SmmUsbDispatch2.h *)
  | gEfiSmmUsbDispatch2ProtocolGuid

  (* Include/Protocol/SmmGpiDispatch2.h *)
  | gEfiSmmGpiDispatch2ProtocolGuid

  (* Include/Protocol/SmmStandbyButtonDispatch2.h *)
  | gEfiSmmStandbyButtonDispatch2ProtocolGuid

  (* Include/Protocol/SmmPowerButtonDispatch2.h *)
  | gEfiSmmPowerButtonDispatch2ProtocolGuid

  (* Include/Protocol/SmmIoTrapDispatch2.h *)
  | gEfiSmmIoTrapDispatch2ProtocolGuid

  (* Include/Protocol/PiPcd.h *)
  | gEfiPcdProtocolGuid

  (* Include/Protocol/FirmwareVolumeBlock.h *)
  | gEfiFirmwareVolumeBlock2ProtocolGuid

  (* Include/Protocol/CpuIo2.h *)
  | gEfiCpuIo2ProtocolGuid

  (* Include/Protocol/LegacyRegion2.h *)
  | gEfiLegacyRegion2ProtocolGuid

  (*
   * Protocols defined in PI 1.2.1
   *)

  (* Include/Protocol/Security2.h *)
  | gEfiSecurity2ArchProtocolGuid

  (* Include/Protocol/SmmEndOfDxe.h *)
  | gEfiSmmEndOfDxeProtocolGuid

  (* Include/Protocol/IsaHc.h *)
  | gEfiIsaHcProtocolGuid
  | gEfiIsaHcServiceBindingProtocolGuid

  (* Include/Protocol/SuperIoControl.h *)
  | gEfiSioControlProtocolGuid

  (* Include/Protocol/PiPcdInfo.h *)
  | gEfiGetPcdInfoProtocolGuid

  (*
   * Protocols defined in PI 1.3.
   *)

  (* Include/Protocol/I2cMaster.h *)
  | gEfiI2cMasterProtocolGuid

  (* Include/Protocol/I2cIo.h *)
  | gEfiI2cIoProtocolGuid

  (* Include/Protocol/I2cEnumerate.h *)
  | gEfiI2cEnumerateProtocolGuid

  (* Include/Protocol/I2cHost.h *)
  | gEfiI2cHostProtocolGuid

  (* Include/Protocol/I2cBusConfigurationManagement.h *)
  | gEfiI2cBusConfigurationManagementProtocolGuid

  (*
   * Protocols defined in PI 1.5.
   *)

  (* Include/Protocol/MmMp.h *)
  | gEfiMmMpProtocolGuid

  (* Include/Protocol/MmEndOfDxe.h *)
  | gEfiMmEndOfDxeProtocolGuid

  (* Include/Protocol/MmIoTrapDispatch.h *)
  | gEfiMmIoTrapDispatchProtocolGuid

  (* Include/Protocol/MmPowerButtonDispatch.h *)
  | gEfiMmPowerButtonDispatchProtocolGuid

  (* Include/Protocol/MmStandbyButtonDispatch.h *)
  | gEfiMmStandbyButtonDispatchProtocolGuid

  (* Include/Protocol/MmGpiDispatch.h *)
  | gEfiMmGpiDispatchProtocolGuid

  (* Include/Protocol/MmUsbDispatch.h *)
  | gEfiMmUsbDispatchProtocolGuid

  (* Include/Protocol/MmPeriodicTimerDispatch.h *)
  | gEfiMmPeriodicTimerDispatchProtocolGuid

  (* Include/Protocol/MmSxDispatch.h *)
  | gEfiMmSxDispatchProtocolGuid

  (* Include/Protocol/MmSwDispatch.h *)
  | gEfiMmSwDispatchProtocolGuid

  (* Include/Protocol/MmPciRootBridgeIo.h *)
  | gEfiMmPciRootBridgeIoProtocolGuid

  (* Include/Protocol/MmCpu.h *)
  | gEfiMmCpuProtocolGuid

  (* Include/Protocol/MmStatusCode.h *)
  | gEfiMmStatusCodeProtocolGuid

  (* Include/Protocol/DxeMmReadyToLock.h *)
  | gEfiDxeMmReadyToLockProtocolGuid

  (* Include/Protocol/MmConfiguration.h *)
  | gEfiMmConfigurationProtocolGuid

  (* Include/Protocol/MmReadyToLock.h *)
  | gEfiMmReadyToLockProtocolGuid

  (* Include/Protocol/MmControl.h *)
  | gEfiMmControlProtocolGuid

  (* Include/Protocol/MmAccess.h *)
  | gEfiMmAccessProtocolGuid

  (* Include/Protocol/MmBase.h *)
  | gEfiMmBaseProtocolGuid

  (* Include/Protocol/MmCpuIo.h *)
  | gEfiMmCpuIoProtocolGuid

  (* Include/Protocol/MmReportStatusCodeHandler.h *)
  | gEfiMmRscHandlerProtocolGuid

  (* Include/Protocol/MmCommunication.h *)
  | gEfiMmCommunicationProtocolGuid

  (*
   * Protocols defined in PI 1.6.
   *)

  (* Include/Protocol/LegacySpiController.h *)
  | gEfiLegacySpiControllerProtocolGuid

  (* Include/Protocol/LegacySpiFlash.h *)
  | gEfiLegacySpiFlashProtocolGuid

  (* Include/Protocol/LegacySpiSmmController.h *)
  | gEfiLegacySpiSmmControllerProtocolGuid

  (* Include/Protocol/LegacySpiSmmFlash.h *)
  | gEfiLegacySpiSmmFlashProtocolGuid

  (* Include/Protocol/SpiConfiguration.h *)
  | gEfiSpiConfigurationProtocolGuid

  (* Include/Protocol/SpiHc.h *)
  | gEfiSpiHcProtocolGuid

  (* Include/Protocol/SpiNorFlash.h *)
  | gEfiSpiNorFlashProtocolGuid

  (* Include/Protocol/SpiSmmConfiguration.h *)
  | gEfiSpiSmmConfigurationProtocolGuid

  (* Include/Protocol/SpiSmmHc.h *)
  | gEfiSpiSmmHcProtocolGuid

  (* Include/Protocol/SpiSmmNorFlash.h *)
  | gEfiSpiSmmNorFlashProtocolGuid

  (*
   * Protocols defined in PI 1.7.
   *)

  (* Include/Protocol/MmCommunication2.h *)
  | gEfiMmCommunication2ProtocolGuid

  (*
   * Protocols defined in UEFI2.1/UEFI2.0/EFI1.1
   *)

  (* Include/Protocol/DebugPort.h *)
  | gEfiDebugPortProtocolGuid

  (* Include/Protocol/DebugSupport.h *)
  | gEfiDebugSupportProtocolGuid

  (* Include/Protocol/Decompress.h *)
  | gEfiDecompressProtocolGuid

  (* Include/Protocol/DeviceIo.h *)
  | gEfiDeviceIoProtocolGuid

  (* Include/Protocol/DevicePath.h *)
  | gEfiDevicePathProtocolGuid

  (* Include/Protocol/DevicePathFromText.h *)
  | gEfiDevicePathFromTextProtocolGuid

  (* Include/Protocol/DevicePathToText.h *)
  | gEfiDevicePathToTextProtocolGuid

  (* Include/Protocol/DevicePathUtilities.h *)
  | gEfiDevicePathUtilitiesProtocolGuid

  (* Include/Protocol/DriverBinding.h *)
  | gEfiDriverBindingProtocolGuid

  (* Include/Protocol/PlatformDriverOverride.h *)
  | gEfiPlatformDriverOverrideProtocolGuid

  (* Include/Protocol/DriverFamilyOverride.h *)
  | gEfiDriverFamilyOverrideProtocolGuid

  (* Include/Protocol/BusSpecificDriverOverride.h *)
  | gEfiBusSpecificDriverOverrideProtocolGuid

  (* Include/Protocol/DriverDiagnostics2.h *)
  | gEfiDriverDiagnostics2ProtocolGuid

  (* Include/Protocol/DriverDiagnostics.h *)
  | gEfiDriverDiagnosticsProtocolGuid

  (* Include/Protocol/ComponentName2.h *)
  | gEfiComponentName2ProtocolGuid

  (* Include/Protocol/ComponentName.h *)
  | gEfiComponentNameProtocolGuid

  (* Include/Protocol/DriverConfiguration2.h *)
  | gEfiDriverConfiguration2ProtocolGuid

  (* Include/Protocol/DriverConfiguration.h *)
  | gEfiDriverConfigurationProtocolGuid

  (* Include/Protocol/PlatformToDriverConfiguration.h *)
  | gEfiPlatformToDriverConfigurationProtocolGuid

  (* Include/Protocol/DriverSupportedEfiVersion.h *)
  | gEfiDriverSupportedEfiVersionProtocolGuid

  (* Include/Protocol/SimpleTextIn.h *)
  | gEfiSimpleTextInProtocolGuid

  (* Include/Protocol/SimpleTextInEx.h *)
  | gEfiSimpleTextInputExProtocolGuid

  (* Include/Protocol/SimpleTextOut.h *)
  | gEfiSimpleTextOutProtocolGuid

  (* Include/Protocol/SimplePointer.h *)
  | gEfiSimplePointerProtocolGuid

  (* Include/Protocol/AbsolutePointer.h *)
  | gEfiAbsolutePointerProtocolGuid

  (* Include/Protocol/SerialIo.h *)
  | gEfiSerialIoProtocolGuid

  (* Include/Protocol/GraphicsOutput.h *)
  | gEfiGraphicsOutputProtocolGuid

  (* Include/Protocol/EdidDiscovered.h *)
  | gEfiEdidDiscoveredProtocolGuid

  (* Include/Protocol/EdidActive.h *)
  | gEfiEdidActiveProtocolGuid

  (* Include/Protocol/EdidOverride.h *)
  | gEfiEdidOverrideProtocolGuid

  (* Include/Protocol/UgaIo.h *)
  | gEfiUgaIoProtocolGuid

  (* Include/Protocol/UgaDraw.h *)
  | gEfiUgaDrawProtocolGuid

  (* Include/Protocol/LoadedImage.h *)
  | gEfiLoadedImageProtocolGuid

  (* Include/Protocol/LoadedImage.h *)
  | gEfiLoadedImageDevicePathProtocolGuid

  (* Include/Protocol/LoadFile.h *)
  | gEfiLoadFileProtocolGuid

  (* Include/Protocol/LoadFile2.h *)
  | gEfiLoadFile2ProtocolGuid

  (* Include/Protocol/SimpleFileSystem.h *)
  | gEfiSimpleFileSystemProtocolGuid

  (* Include/Protocol/TapeIo.h *)
  | gEfiTapeIoProtocolGuid

  (* Include/Protocol/DiskIo.h *)
  | gEfiDiskIoProtocolGuid

  (* Include/Protocol/BlockIo.h *)
  | gEfiBlockIoProtocolGuid

  (* Include/Protocol/UnicodeCollation.h *)
  | gEfiUnicodeCollationProtocolGuid

  (* Include/Protocol/UnicodeCollation.h *)
  | gEfiUnicodeCollation2ProtocolGuid

  (* Include/Protocol/PciRootBridgeIo.h *)
  | gEfiPciRootBridgeIoProtocolGuid

  (* Include/Protocol/PciIo.h *)
  | gEfiPciIoProtocolGuid

  (* Include/Protocol/ScsiIo.h *)
  | gEfiScsiIoProtocolGuid

  (* Include/Protocol/ScsiPassThruExt.h *)
  | gEfiExtScsiPassThruProtocolGuid

  (* Include/Protocol/ScsiPassThru.h *)
  | gEfiScsiPassThruProtocolGuid

  (* Include/Protocol/IScsiInitiatorName.h *)
  | gEfiIScsiInitiatorNameProtocolGuid

  (* Include/Protocol/Usb2HostController.h *)
  | gEfiUsb2HcProtocolGuid

  (* Include/Protocol/UsbHostController.h *)
  | gEfiUsbHcProtocolGuid

  (* Include/Protocol/UsbIo.h *)
  | gEfiUsbIoProtocolGuid

  (* Include/Protocol/AcpiTable.h *)
  | gEfiAcpiTableProtocolGuid

  (* Include/Protocol/Ebc.h *)
  | gEfiEbcProtocolGuid

  (* Include/Protocol/SimpleNetwork.h *)
  | gEfiSimpleNetworkProtocolGuid

  (* Include/Protocol/NetworkInterfaceIdentifier.h *)
  | gEfiNetworkInterfaceIdentifierProtocolGuid_31

  (* Include/Protocol/NetworkInterfaceIdentifier.h *)
  | gEfiNetworkInterfaceIdentifierProtocolGuid

  (* Include/Protocol/PxeBaseCodeCallBack.h *)
  | gEfiPxeBaseCodeCallbackProtocolGuid

  (* Include/Protocol/PxeBaseCode.h *)
  | gEfiPxeBaseCodeProtocolGuid

  (* Include/Protocol/Bis.h *)
  | gEfiBisProtocolGuid

  (* Include/Protocol/ManagedNetwork.h *)
  | gEfiManagedNetworkServiceBindingProtocolGuid

  (* Include/Protocol/ManagedNetwork.h *)
  | gEfiManagedNetworkProtocolGuid

  (* Include/Protocol/Arp.h *)
  | gEfiArpServiceBindingProtocolGuid

  (* Include/Protocol/Arp.h *)
  | gEfiArpProtocolGuid

  (* Include/Protocol/Dhcp4.h *)
  | gEfiDhcp4ServiceBindingProtocolGuid

  (* Include/Protocol/Dhcp4.h *)
  | gEfiDhcp4ProtocolGuid

  (* Include/Protocol/Tcp4.h *)
  | gEfiTcp4ServiceBindingProtocolGuid

  (* Include/Protocol/Tcp4.h *)
  | gEfiTcp4ProtocolGuid

  (* Include/Protocol/Ip4.h *)
  | gEfiIp4ServiceBindingProtocolGuid

  (* Include/Protocol/Ip4.h *)
  | gEfiIp4ProtocolGuid

  (* Include/Protocol/Ip4Config.h *)
  | gEfiIp4ConfigProtocolGuid

  (* Include/Protocol/Udp4.h *)
  | gEfiUdp4ServiceBindingProtocolGuid

  (* Include/Protocol/Udp4.h *)
  | gEfiUdp4ProtocolGuid

  (* Include/Protocol/Mtftp4.h *)
  | gEfiMtftp4ServiceBindingProtocolGuid

  (* Include/Protocol/Mtftp4.h *)
  | gEfiMtftp4ProtocolGuid

  (* Include/Protocol/AuthenticationInfo.h *)
  | gEfiAuthenticationInfoProtocolGuid

  (* Include/Protocol/Hash.h *)
  | gEfiHashServiceBindingProtocolGuid

  (* Include/Protocol/Hash.h *)
  | gEfiHashProtocolGuid

  (* Include/Protocol/TcgService.h *)
  | gEfiTcgProtocolGuid

  (* Include/Protocol/TrEEProtocol.h *)
  | gEfiTrEEProtocolGuid

  (* Include/Protocol/Tcg2Protocol.h *)
  | gEfiTcg2ProtocolGuid
  | gEfiTcg2FinalEventsTableGuid

  (* Include/Protocol/FormBrowser2.h *)
  | gEfiFormBrowser2ProtocolGuid

  (* Include/Protocol/HiiString.h *)
  | gEfiHiiStringProtocolGuid

  (* Include/Protocol/HiiImage.h *)
  | gEfiHiiImageProtocolGuid

  (* Include/Protocol/HiiConfigRouting.h *)
  | gEfiHiiConfigRoutingProtocolGuid

  (* Include/Protocol/HiiDatabase.h *)
  | gEfiHiiDatabaseProtocolGuid

  (* Include/Protocol/HiiFont.h *)
  | gEfiHiiFontProtocolGuid

  (* Include/Protocol/HiiConfigAccess.h *)
  | gEfiHiiConfigAccessProtocolGuid

  (* Include/Protocol/HiiPackageList.h *)
  | gEfiHiiPackageListProtocolGuid

  (*
   * Protocols defined in UEFI2.2
   *)

  (* Include/Protocol/Ip6.h *)
  | gEfiIp6ServiceBindingProtocolGuid

  (* Include/Protocol/Ip6.h *)
  | gEfiIp6ProtocolGuid

  (* Include/Protocol/Ip6Config.h *)
  | gEfiIp6ConfigProtocolGuid

  (* Include/Protocol/Mtftp6.h *)
  | gEfiMtftp6ServiceBindingProtocolGuid

  (* Include/Protocol/Mtftp6.h *)
  | gEfiMtftp6ProtocolGuid

  (* Include/Protocol/Dhcp6.h *)
  | gEfiDhcp6ServiceBindingProtocolGuid

  (* Include/Protocol/Dhcp6.h *)
  | gEfiDhcp6ProtocolGuid

  (* Include/Protocol/Udp6.h *)
  | gEfiUdp6ServiceBindingProtocolGuid

  (* Include/Protocol/Udp6.h *)
  | gEfiUdp6ProtocolGuid

  (* Include/Protocol/Tcp6.h *)
  | gEfiTcp6ServiceBindingProtocolGuid

  (* Include/Protocol/Tcp6.h *)
  | gEfiTcp6ProtocolGuid

  (* Include/Protocol/VlanConfig.h *)
  | gEfiVlanConfigProtocolGuid

  (* Include/Protocol/Eap.h *)
  | gEfiEapProtocolGuid

  (* Include/Protocol/EapManagement.h *)
  | gEfiEapManagementProtocolGuid

  (* Include/Protocol/Ftp4.h *)
  | gEfiFtp4ServiceBindingProtocolGuid

  (* Include/Protocol/Ftp4.h *)
  | gEfiFtp4ProtocolGuid

  (* Include/Protocol/IpSecConfig.h *)
  | gEfiIpSecConfigProtocolGuid

  (* Include/Protocol/DriverHealth.h *)
  | gEfiDriverHealthProtocolGuid

  (* Include/Protocol/DeferredImageLoad.h *)
  | gEfiDeferredImageLoadProtocolGuid

  (* Include/Protocol/UserCredential.h *)
  | gEfiUserCredentialProtocolGuid

  (* Include/Protocol/UserManager.h *)
  | gEfiUserManagerProtocolGuid

  (* Include/Protocol/AtaPassThru.h *)
  | gEfiAtaPassThruProtocolGuid

  (*
   * Protocols defined in UEFI2.3
   *)

  (* Include/Protocol/FirmwareManagement.h *)
  | gEfiFirmwareManagementProtocolGuid

  (* Include/Protocol/IpSec.h *)
  | gEfiIpSecProtocolGuid

  (* Include/Protocol/IpSec.h *)
  | gEfiIpSec2ProtocolGuid

  (*
   * Protocols defined in UEFI2.3.1
   *)

  (* Include/Protocol/Kms.h *)
  | gEfiKmsProtocolGuid

  (* Include/Protocol/BlockIo2.h *)
  | gEfiBlockIo2ProtocolGuid

  (* Include/Protocol/StorageSecurityCommand.h *)
  | gEfiStorageSecurityCommandProtocolGuid

  (* Include/Protocol/UserCredential2.h *)
  | gEfiUserCredential2ProtocolGuid

  (*
   * Protocols defined in UEFI2.4
   *)

  (* Include/Protocol/DiskIo2.h *)
  | gEfiDiskIo2ProtocolGuid

  (* Include/Protocol/Timestamp.h *)
  | gEfiTimestampProtocolGuid

  (* Include/Protocol/Rng.h *)
  | gEfiRngProtocolGuid

  (* Include/Protocol/AdapterInformation.h *)
  | gEfiAdapterInformationProtocolGuid

  (*
   * Protocols defined in UEFI2.5
   *)

  (* Include/Protocol/NvmExpressPassthru.h *)
  | gEfiNvmExpressPassThruProtocolGuid

  (* Include/Protocol/Hash2.h *)
  | gEfiHash2ServiceBindingProtocolGuid

  (* Include/Protocol/Hash2.h *)
  | gEfiHash2ProtocolGuid

  (* Include/Protocol/BlockIoCrypto.h *)
  | gEfiBlockIoCryptoProtocolGuid

  (* Include/Protocol/SmartCardReader.h *)
  | gEfiSmartCardReaderProtocolGuid
  | gEfiSmartCardEdgeProtocolGuid
  | gEfiUsbFunctionIoProtocolGuid
  | gEfiBluetoothHcProtocolGuid
  | gEfiBluetoothIoServiceBindingProtocolGuid
  | gEfiBluetoothIoProtocolGuid
  | gEfiBluetoothConfigProtocolGuid
  | gEfiRegularExpressionProtocolGuid
  | gEfiBootManagerPolicyProtocolGuid
  | gEfiConfigKeywordHandlerProtocolGuid
  | gEfiWiFiProtocolGuid
  | gEfiEapManagement2ProtocolGuid
  | gEfiEapConfigurationProtocolGuid
  | gEfiPkcs7VerifyProtocolGuid
  | gEfiIp4Config2ProtocolGuid
  | gEfiDns4ServiceBindingProtocolGuid
  | gEfiDns4ProtocolGuid
  | gEfiDns6ServiceBindingProtocolGuid
  | gEfiDns6ProtocolGuid
  | gEfiHttpServiceBindingProtocolGuid
  | gEfiHttpProtocolGuid
  | gEfiHttpUtilitiesProtocolGuid
  | gEfiTlsServiceBindingProtocolGuid
  | gEfiTlsProtocolGuid
  | gEfiTlsConfigurationProtocolGuid
  | gEfiRestProtocolGuid
  | gEfiSupplicantServiceBindingProtocolGuid
  | gEfiSupplicantProtocolGuid
  | gEfiWiFi2ProtocolGuid
  | gEfiRamDiskProtocolGuid
  | gEfiHiiImageDecoderProtocolGuid
  | gEfiHiiImageExProtocolGuid
  | gEfiSdMmcPassThruProtocolGuid
  | gEfiEraseBlockProtocolGuid
  | gEfiBluetoothAttributeProtocolGuid
  | gEfiBluetoothAttributeServiceBindingProtocolGuid
  | gEfiBluetoothLeConfigProtocolGuid
  | gEfiUfsDeviceConfigProtocolGuid
  | gEfiHttpBootCallbackProtocolGuid
  | gEfiResetNotificationProtocolGuid
  | gEfiPartitionInfoProtocolGuid
  | gEfiHiiPopupProtocolGuid
  | gEfiNvdimmLabelProtocolGuid
  | gEfiRestExProtocolGuid
  | gEfiRestExServiceBindingProtocolGuid
  | gEfiRestJsonStructureProtocolGuid
  | gEfiRedfishDiscoverProtocolGuid
  | gEfiShellProtocolGuid
  | gEfiShellParametersProtocolGuid
  | gEfiShellDynamicCommandProtocolGuid
].
