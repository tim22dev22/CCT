let interval=1000, startingInterval=1000, maximumInterval=1000, minimumInterval=200;
let intervalIncrement=100;
let scoredItemCount=0, totalResponseTime=0;
let correctResponseTimes=[];
let stimulusCount=0, stimulusHistory=[];
let correctStreak=0, wrongStreak=0;
let gameRunning=false, timeoutId, endTime;
let awaitingAnswer=false, beepEnabled=true;
let sessionState="idle";
let isStimulusTick=false;
let stimulusScheduleSerial=0;
let lastStimulusAt=0;
let endCondition="timer", targetCorrect=50, correctAnswers=0;
let arithmeticMode="addition";
let nBackLevel=1;
let sessionStartedAt=0, sessionEndedAt=0;
let responseStartedAt=0, responseInterval=0;
let excludeLastQuestionFromTrace=false;
let sessionOutcome="Completed";
let currentSessionId="";
let historyVisible=false;
let historyFilterVisible=false;
let historyStatsGlossaryPinned=false;
let historyStatsGlossaryEscapeDismissed=false;
let sessionIntervalTrace=[];
let activeQuestionState=null;
let historyChartMode=null;
let historyChartModeIsUserSelected=false;
let historyChartNBackLevel=null;
let historyChartNBackLevelIsUserSelected=false;
let historyPageIndex=0;
let historyTrendRefreshToken=0;
let historySessionRefreshToken=0;
let settingsSaveTimerId=null;
let intervalStatsTimerId=null;
let countdownTimerId=null;
let profiles=[];
let activeProfileId="";
let profileNameDialogAction=null;
let profileNameDialogTrigger=null;
let confirmationDialogAction=null;
let confirmationDialogTrigger=null;
let confirmationDialogFocusTimerId=null;
const HISTORY_PAGE_SIZE=20;
const historyFilters={
  status:"all",
  mode:"all",
  nBackLevel:"all",
  trendInclusion:"all"
};
const EMPTY_HISTORY_STATS={
  completedSessions:0,
  totalCorrectAnswers:0,
  totalDurationMs:0
};
const SETTINGS_KEY="cctSettings";
const PROFILES_KEY="cctProfiles";
const LEGACY_PRESETS_KEY="cctPresets";
const PROFILES_SCHEMA_VERSION=1;
const MAX_PROFILE_NAME_LENGTH=60;
const ARITHMETIC_MODES=new Set(["addition","multiplication","subtraction","difference"]);
const MIN_N_BACK_LEVEL=1;
const MAX_N_BACK_LEVEL=5;
const DEFAULT_BEEP_GAIN=0.12;
const DEFAULT_BEEP_VOLUME_PERCENT=50;
const MAX_BEEP_VOLUME_PERCENT=100;
const MAX_BEEP_GAIN=0.9;
const MIN_INTERVAL_VALUE=100;
const MAX_INTERVAL_VALUE=3000;
const defaultSettings={
  startingInterval:"3000",
  maximumInterval:"3000",
  minimumInterval:"700",
  intervalIncrement:"100",
  correctThreshold:"4",
  incorrectThreshold:"4",
  duration:"15",
  endCondition:"timer",
  targetCorrect:"500",
  mode:"addition",
  nBackLevel:"1",
  voice:"nathan",
  playbackSpeed:"1",
  beepVolume:String(DEFAULT_BEEP_VOLUME_PERCENT),
  beepEnabled:true,
  darkMode:false,
  showAdvancedSettings:false,
  showIntervalTiming:false,
  hideTimerDuringSession:false
};

let intervalCounts={}, intervalTime={}, currentIntervalStart=0;
let sortedIntervalKeys=[];
let intervalKeysDirty=true;
let feedbackIndicatorColor=null, feedbackIndicatorCount=0;
let showIntervalTiming=false;
let selectedVoice="";
let playbackSpeed=1;
let beepVolume=DEFAULT_BEEP_VOLUME_PERCENT;
let hideTimerDuringSession=false;
let sessionTimerVisible=true;
let voiceAudioCache={};
let activeStimulusAudios=new Set();
let voiceLibrary={};
let voiceTestInProgress=false;
let beepAudioContext=null;

function clampInteger(value,fallback,min,max){
  const parsed=parseInt(value,10);
  if(Number.isNaN(parsed)) return fallback;
  return Math.max(min,Math.min(max,parsed));
}

function parsePositiveInteger(value,fallback,min=1){
  return Math.max(min,parseInt(value,10)||parseInt(fallback,10));
}

function coercePositiveNumber(value,fallback,min=1){
  return Math.max(min,Number(value)||Number(fallback)||min);
}

function normalizeOptionalNonNegativeNumber(value){
  if(value===null || value===undefined || value==="") return null;
  const parsed=Number(value);
  return Number.isFinite(parsed) && parsed>=0 ? parsed : null;
}

function calculateMedianFromSortedValues(sortedValues){
  if(!sortedValues.length) return null;
  const middle=Math.floor(sortedValues.length/2);
  return sortedValues.length%2
    ? sortedValues[middle]
    : (sortedValues[middle-1]+sortedValues[middle])/2;
}

function calculatePercentile(sortedValues,percentile){
  if(!sortedValues.length) return null;
  const position=(sortedValues.length-1)*percentile;
  const lower=Math.floor(position);
  const upper=Math.ceil(position);
  if(lower===upper) return sortedValues[lower];
  const weight=position-lower;
  return sortedValues[lower] + (sortedValues[upper]-sortedValues[lower])*weight;
}

function calculateResponseTimeStats(values){
  const sorted=(Array.isArray(values) ? values : [])
    .filter(value=>Number.isFinite(Number(value)) && Number(value)>=0)
    .map(Number)
    .sort((a,b)=>a-b);
  if(!sorted.length){
    return { medianResponseTimeMs:null, responseTimeIqrMs:null };
  }

  const medianResponseTimeMs=calculateMedianFromSortedValues(sorted);
  const firstQuartile=calculatePercentile(sorted,0.25);
  const thirdQuartile=calculatePercentile(sorted,0.75);
  return {
    medianResponseTimeMs,
    responseTimeIqrMs:thirdQuartile-firstQuartile
  };
}

function clampBeepVolumePercent(value,fallback=defaultSettings.beepVolume){
  const parsed=Number(value);
  const fallbackParsed=Number(fallback);
  const resolved=Number.isFinite(parsed) ? parsed : (Number.isFinite(fallbackParsed) ? fallbackParsed : DEFAULT_BEEP_VOLUME_PERCENT);
  return Math.max(0,Math.min(MAX_BEEP_VOLUME_PERCENT,resolved));
}

function normalizeBeepVolumeSetting(value,fallback=defaultSettings.beepVolume){
  const parsed=Number(value);
  if(!Number.isInteger(parsed) || parsed<0 || parsed>MAX_BEEP_VOLUME_PERCENT){
    return clampBeepVolumePercent(fallback);
  }
  return parsed;
}

function normalizeNBackLevel(value,fallback=defaultSettings.nBackLevel){
  const parsed=Number(value);
  const fallbackParsed=Number(fallback);
  const resolved=Number.isInteger(parsed) ? parsed : (Number.isInteger(fallbackParsed) ? fallbackParsed : MIN_N_BACK_LEVEL);
  return Math.max(MIN_N_BACK_LEVEL,Math.min(MAX_N_BACK_LEVEL,resolved));
}

function getBeepGain(){
  const level=normalizeBeepVolumeSetting(beepVolume)/MAX_BEEP_VOLUME_PERCENT;
  return Math.pow(level,2)*MAX_BEEP_GAIN;
}

function normalizeVoiceKey(value){
  if(typeof value!=="string") return "";
  return value.trim().toLowerCase().replace(/[\s_-]+/g,"");
}

function resolveVoiceKey(value,fallbackKey=defaultSettings.voice){
  const normalized=normalizeVoiceKey(value);
  if(normalized && voiceLibrary[normalized]) return normalized;
  if(fallbackKey && voiceLibrary[fallbackKey]) return fallbackKey;
  return Object.keys(voiceLibrary)[0] || fallbackKey;
}

function normalizeSavedSettings(parsed){
  const startingFallback=clampInteger(parsed.startingInterval ?? parsed.interval,defaultSettings.startingInterval,MIN_INTERVAL_VALUE,MAX_INTERVAL_VALUE);
  const minimumFallback=clampInteger(parsed.minimumInterval,defaultSettings.minimumInterval,MIN_INTERVAL_VALUE,MAX_INTERVAL_VALUE);
  const maximumFallback=clampInteger(parsed.maximumInterval,defaultSettings.maximumInterval,MIN_INTERVAL_VALUE,MAX_INTERVAL_VALUE);
  const maximumIntervalValue=Math.max(MIN_INTERVAL_VALUE,minimumFallback,startingFallback,maximumFallback);
  const minimumInterval=String(minimumFallback);
  const startingInterval=String(Math.max(
    parseInt(minimumInterval,10),
    Math.min(startingFallback,maximumIntervalValue)
  ));
  const maximumInterval=String(maximumIntervalValue);
  const intervalIncrement=String(clampInteger(parsed.intervalIncrement,defaultSettings.intervalIncrement,10,100));
  const correctThreshold=String(clampInteger(parsed.correctThreshold,defaultSettings.correctThreshold,1,10));
  const incorrectThreshold=String(clampInteger(parsed.incorrectThreshold,defaultSettings.incorrectThreshold,1,10));
  const duration=String(Math.max(1,clampInteger(parsed.duration,defaultSettings.duration,1,9999)));
  const targetCorrect=String(Math.max(1,clampInteger(parsed.targetCorrect,defaultSettings.targetCorrect,1,9999)));
  const mode=ARITHMETIC_MODES.has(parsed.mode) ? parsed.mode : defaultSettings.mode;
  const nBackLevel=String(normalizeNBackLevel(parsed.nBackLevel));
  const voice=resolveVoiceKey(parsed.voice,defaultSettings.voice);
  const beepVolume=String(normalizeBeepVolumeSetting(parsed.beepVolume,defaultSettings.beepVolume));

  const normalized={
    ...defaultSettings,
    ...parsed,
    startingInterval,
    maximumInterval,
    minimumInterval,
    intervalIncrement,
    correctThreshold,
    incorrectThreshold,
    duration,
    targetCorrect,
    mode,
    nBackLevel,
    voice,
    playbackSpeed:String(Math.max(1,Math.min(1.5,parseFloat(parsed.playbackSpeed)||parseFloat(defaultSettings.playbackSpeed)))),
    beepVolume,
    showAdvancedSettings:!!parsed.showAdvancedSettings,
    showIntervalTiming:!!parsed.showIntervalTiming,
    hideTimerDuringSession:!!parsed.hideTimerDuringSession,
    beepEnabled:parsed.beepEnabled ?? defaultSettings.beepEnabled,
    darkMode:parsed.darkMode ?? defaultSettings.darkMode
  };
  delete normalized.preferredStartingInterval;
  delete normalized.preferredMaximumInterval;
  delete normalized.preferredMinimumInterval;
  delete normalized.intervalPreferenceOrder;
  return normalized;
}

function updateAppViews(){
  const sessionVisible=sessionState==="starting"||sessionState==="active";
  const resultsVisible=sessionState==="results";
  const settingsVisible=sessionState==="idle"&&!historyVisible;
  const historyPageVisible=historyVisible;

  document.body.classList.toggle("session-in-progress",sessionVisible);
  sessionView.classList.toggle("hidden",!sessionVisible);
  resultsView.classList.toggle("hidden",!resultsVisible);
  historyView.classList.toggle("hidden",!historyPageVisible);
  settingsView.classList.toggle("hidden",!settingsVisible);
  footerView.classList.toggle("hidden",!settingsVisible);
  startBtn.disabled=sessionState!=="idle";
  answer.disabled=sessionState!=="active";
  endSessionBtn.disabled=!sessionVisible;
  toggleSessionTimerBtn.disabled=sessionState!=="active" || endCondition!=="timer";
}

function hideHistoryFilters(){
  historyFilterVisible=false;
  if(historyFiltersPanel){
    historyFiltersPanel.classList.add("hidden");
  }
  if(historyFilterBtn){
    historyFilterBtn.setAttribute("aria-expanded","false");
  }
}

function setSessionState(nextState){
  sessionState=nextState;
  if(nextState!=="idle"){
    historyVisible=false;
  }
  updateAppViews();
}

function setHistoryVisible(isVisible){
  historyVisible=isVisible;
  hideHistoryFilters();
  if(isVisible){
    sessionState="idle";
  }
  updateAppViews();
}

function readSavedSettings(){
  try{
    const saved=window.localStorage.getItem(SETTINGS_KEY);
    if(!saved) return {...defaultSettings};
    const parsed=JSON.parse(saved);
    const normalized=normalizeSavedSettings(parsed);
    if(saved!==JSON.stringify(normalized)){
      window.localStorage.setItem(SETTINGS_KEY,JSON.stringify(normalized));
    }
    return normalized;
  }catch(e){
    return {...defaultSettings};
  }
}

function getSettingsFromForm(){
  return {
    startingInterval:startingIntervalInput.value,
    maximumInterval:maximumIntervalInput.value,
    minimumInterval:minimumIntervalInput.value,
    intervalIncrement:intervalIncrementSelect.value,
    correctThreshold:correctThresholdInput.value,
    incorrectThreshold:incorrectThresholdInput.value,
    duration:durationInput.value,
    endCondition:endConditionSelect.value,
    targetCorrect:targetCorrectInput.value,
    mode:modeSelect.value,
    nBackLevel:String(normalizeNBackLevel(nBackLevelInput.value)),
    voice:resolveVoiceKey(voiceSelect.value || selectedVoice),
    playbackSpeed:playbackSpeedSelect.value,
    beepVolume:beepVolumeSelect.value,
    beepEnabled:beepToggle.checked,
    darkMode:themeToggle.getAttribute("aria-pressed")==="true",
    showAdvancedSettings:showAdvancedSettingsToggle.checked,
    showIntervalTiming:showIntervalTimingToggle.checked,
    hideTimerDuringSession:hideTimerDuringSessionToggle.checked
  };
}

function normalizeProfileName(value){
  return String(value??"").normalize("NFKC").trim().replace(/\s+/g," ");
}

function getProfileNameKey(value){
  return normalizeProfileName(value).toLocaleLowerCase();
}

function normalizeProfileSettings(settings){
  const normalized=normalizeSavedSettings(settings);
  delete normalized.darkMode;
  delete normalized.showAdvancedSettings;
  return normalized;
}

function generateProfileId(){
  if(window.crypto && typeof window.crypto.randomUUID==="function"){
    return window.crypto.randomUUID();
  }
  return "profile_" + Date.now() + "_" + Math.random().toString(36).slice(2,10);
}

function getUniqueProfileName(value,usedNames){
  const baseName=normalizeProfileName(value) || "Profile";
  const trimmedBase=baseName.slice(0,MAX_PROFILE_NAME_LENGTH);
  let name=trimmedBase;
  let suffixNumber=2;
  while(usedNames.has(getProfileNameKey(name))){
    const suffix=` (${suffixNumber++})`;
    name=trimmedBase.slice(0,MAX_PROFILE_NAME_LENGTH-suffix.length) + suffix;
  }
  usedNames.add(getProfileNameKey(name));
  return name;
}

function normalizeProfileList(records){
  const usedNames=new Set();
  const usedIds=new Set();
  return records.reduce((result,record)=>{
    if(!record || !record.settings) return result;
    let id=String(record.id||generateProfileId());
    while(usedIds.has(id)) id=generateProfileId();
    usedIds.add(id);
    result.push({
      id,
      name:getUniqueProfileName(record.name,usedNames),
      settings:normalizeProfileSettings(record.settings),
      createdAt:Number(record.createdAt)||Date.now(),
      updatedAt:Number(record.updatedAt)||Number(record.createdAt)||Date.now()
    });
    return result;
  },[]);
}

function readLegacyPresets(){
  try{
    const raw=window.localStorage.getItem(LEGACY_PRESETS_KEY);
    if(!raw) return [];
    const parsed=JSON.parse(raw);
    const records=Array.isArray(parsed) ? parsed : parsed?.presets;
    return Array.isArray(records) ? records : [];
  }catch(e){
    return [];
  }
}

function readSavedProfiles(){
  try{
    const raw=window.localStorage.getItem(PROFILES_KEY);
    if(raw){
      const parsed=JSON.parse(raw);
      const records=Array.isArray(parsed) ? parsed : parsed?.profiles;
      const normalized=normalizeProfileList(Array.isArray(records) ? records : []);
      if(normalized.length){
        const requestedId=String(parsed?.activeProfileId||"");
        const active=normalized.find(profile=>profile.id===requestedId) || normalized[0];
        return { profiles:normalized, activeProfileId:active.id };
      }
    }

    const legacyRecords=readLegacyPresets();
    const migrationRecords=[
      { id:generateProfileId(), name:"Default", settings:readSavedSettings() },
      ...legacyRecords
    ];
    const migrated=normalizeProfileList(migrationRecords);
    const active=migrated[0];
    return {
      profiles:migrated.length ? migrated : normalizeProfileList([{ name:"Default", settings:defaultSettings }]),
      activeProfileId:active?.id || ""
    };
  }catch(e){
    const fallback={id:generateProfileId(),name:"Default",settings:defaultSettings};
    return { profiles:normalizeProfileList([fallback]), activeProfileId:fallback.id };
  }
}

function persistProfiles(options={}){
  try{
    const latest=readStoredProfileState();
    const deletedIds=new Set(options.deletedIds||[]);
    const localById=new Map(profiles.map(profile=>[profile.id,profile]));
    const merged=[];
    latest.profiles.forEach(profile=>{
      if(deletedIds.has(profile.id)) return;
      const local=localById.get(profile.id);
      merged.push(local && Number(local.updatedAt)>=Number(profile.updatedAt) ? local : profile);
      localById.delete(profile.id);
    });
    localById.forEach(profile=>merged.push(profile));
    const nextProfiles=normalizeProfileList(merged);
    const nextActiveProfileId=nextProfiles.some(profile=>profile.id===activeProfileId)
      ? activeProfileId
      : latest.activeProfileId || nextProfiles[0]?.id || "";
    window.localStorage.setItem(PROFILES_KEY,JSON.stringify({
      schemaVersion:PROFILES_SCHEMA_VERSION,
      activeProfileId:nextActiveProfileId,
      profiles:nextProfiles
    }));
    profiles=nextProfiles;
    activeProfileId=nextActiveProfileId;
    return true;
  }catch(e){
    return false;
  }
}

function readStoredProfileState(){
  try{
    const raw=window.localStorage.getItem(PROFILES_KEY);
    if(!raw) return {profiles:[],activeProfileId:""};
    const parsed=JSON.parse(raw);
    const records=Array.isArray(parsed) ? parsed : parsed?.profiles;
    const normalized=normalizeProfileList(Array.isArray(records)?records:[]);
    return {profiles:normalized,activeProfileId:String(parsed?.activeProfileId||normalized[0]?.id||"")};
  }catch(e){
    return {profiles:[],activeProfileId:""};
  }
}

function findProfileById(id){
  return profiles.find(profile=>profile.id===id) || null;
}

function profileNameExists(name,excludedId=""){
  const nameKey=getProfileNameKey(name);
  return profiles.some(profile=>profile.id!==excludedId && getProfileNameKey(profile.name)===nameKey);
}

function setProfileStatus(message,type=""){
  profileStatus.textContent=message;
  profileStatus.classList.toggle("is-error",type==="error");
  profileStatus.classList.toggle("is-success",type==="success");
}

function renderProfileOptions(selectedId=activeProfileId){
  const sorted=[...profiles].sort((a,b)=>a.name.localeCompare(b.name,undefined,{ sensitivity:"base" }));
  profileSelect.replaceChildren();
  sorted.forEach(profile=>{
    const option=document.createElement("option");
    option.value=profile.id;
    option.textContent=profile.name;
    profileSelect.append(option);
  });
  if(sorted.length){
    profileSelect.value=findProfileById(selectedId) ? selectedId : sorted[0].id;
  }
  updateProfileActionState();
}

function updateProfileActionState(){
  const hasActiveProfile=!!findProfileById(activeProfileId);
  renameProfileBtn.disabled=!hasActiveProfile;
  deleteProfileBtn.disabled=!hasActiveProfile || profiles.length<=1;
}

function getSelectedProfileSource(){
  const selected=document.querySelector("input[name=profileSource]:checked");
  return selected?.value==="default" ? "default" : "current";
}

function openProfileNameDialog(action,profile=null){
  profileNameDialogAction={ action, profileId:profile?.id || "" };
  profileNameDialogTrigger=document.activeElement;
  const isRename=action==="rename";
  profileNameDialogTitle.textContent=isRename ? "Rename Profile" : "New Profile";
  confirmProfileNameBtn.textContent=isRename ? "Rename Profile" : "Create Profile";
  profileNameInput.value=isRename ? profile.name : getNextProfileName();
  profileSourceField.classList.toggle("hidden",isRename);
  if(!isRename){
    const currentSource=document.querySelector("input[name=profileSource][value=current]");
    if(currentSource) currentSource.checked=true;
  }
  profileNameError.textContent="";
  profileNameInput.removeAttribute("aria-invalid");
  profileNameDialog.showModal();
  setTimeout(()=>{
    profileNameInput.focus();
    profileNameInput.select();
  },0);
}

function getNextProfileName(){
  const usedNames=new Set(profiles.map(profile=>getProfileNameKey(profile.name)));
  let number=1;
  while(usedNames.has(getProfileNameKey(`Profile ${number}`))) number+=1;
  return `Profile ${number}`;
}

function setProfileDialogError(message){
  if(profileNameDialog?.open){
    profileNameError.textContent=message;
    profileNameInput.setAttribute("aria-invalid","true");
    profileNameInput.focus();
  }else setProfileStatus(message,"error");
}

function closeProfileNameDialog(){
  if(profileNameDialog.open){
    profileNameDialog.close();
  }
}

function openConfirmationDialog({ title, message, confirmLabel="Confirm", onConfirm }){
  if(confirmationDialog.open) return;
  if(confirmationDialogFocusTimerId!==null){
    clearTimeout(confirmationDialogFocusTimerId);
    confirmationDialogFocusTimerId=null;
  }
  confirmationDialogAction=onConfirm;
  confirmationDialogTrigger=document.activeElement;
  confirmationDialogTitle.textContent=title;
  confirmationDialogMessage.textContent=message;
  confirmConfirmationBtn.textContent=confirmLabel;
  confirmationDialog.showModal();
  confirmationDialogFocusTimerId=setTimeout(()=>{
    confirmationDialogFocusTimerId=null;
    if(confirmationDialog.open) cancelConfirmationBtn.focus();
  },0);
}

function closeConfirmationDialog(){
  if(confirmationDialogFocusTimerId!==null){
    clearTimeout(confirmationDialogFocusTimerId);
    confirmationDialogFocusTimerId=null;
  }
  if(confirmationDialog.open){
    confirmationDialog.close();
  }
}

function submitConfirmationDialog(event){
  event.preventDefault();
  const action=confirmationDialogAction;
  closeConfirmationDialog();
  if(typeof action==="function") void action();
}

function createProfile(name,settings){
  if(profileNameExists(name)){
    setProfileDialogError(`A profile named “${name}” already exists.`);
    return false;
  }
  if(activeProfileId) saveSettings();
  const previousActiveProfileId=activeProfileId;
  const now=Date.now();
  const profile={
    id:generateProfileId(),
    name,
    settings:normalizeProfileSettings(settings),
    createdAt:now,
    updatedAt:now
  };
  profiles.push(profile);
  activeProfileId=profile.id;
  if(!persistProfiles()){
    profiles=profiles.filter(item=>item.id!==profile.id);
    activeProfileId=previousActiveProfileId;
    setProfileDialogError("This browser could not save the profile. Try again.");
    return false;
  }
  applySettings({
    ...profile.settings,
    showAdvancedSettings:showAdvancedSettingsToggle.checked,
    darkMode:themeToggle.getAttribute("aria-pressed")==="true"
  });
  saveSettings();
  renderProfileOptions(profile.id);
  setProfileStatus("");
  return true;
}

function activateProfile(profileId){
  const profile=findProfileById(profileId);
  if(!profile || profile.id===activeProfileId) return;
  saveSettings();
  const previousActiveProfileId=activeProfileId;
  activeProfileId=profile.id;
  profile.settings=normalizeProfileSettings(profile.settings);
  if(!persistProfiles()){
    activeProfileId=previousActiveProfileId;
    profileSelect.value=previousActiveProfileId;
    setProfileStatus("This browser could not switch profiles.","error");
    return;
  }
  applySettings({
    ...profile.settings,
    showAdvancedSettings:showAdvancedSettingsToggle.checked,
    darkMode:themeToggle.getAttribute("aria-pressed")==="true"
  });
  saveSettings();
  renderProfileOptions(profile.id);
  setProfileStatus("");
}

function renameSelectedProfile(){
  const profile=findProfileById(activeProfileId);
  if(!profile) return;
  openProfileNameDialog("rename",profile);
}

function renameProfile(profile,name){
  if(profileNameExists(name,profile.id)){
    setProfileDialogError(`A profile named “${name}” already exists.`);
    return false;
  }
  saveSettings();
  const previousName=profile.name;
  profile.name=name;
  profile.updatedAt=Date.now();
  if(!persistProfiles()){
    profile.name=previousName;
    setProfileDialogError("This browser could not rename the profile. Try again.");
    return false;
  }
  renderProfileOptions(profile.id);
  setProfileStatus("");
  return true;
}

function submitProfileNameDialog(event){
  event.preventDefault();
  const name=normalizeProfileName(profileNameInput.value);
  if(!name){
    profileNameError.textContent="Enter a name for this profile.";
    profileNameInput.setAttribute("aria-invalid","true");
    profileNameInput.focus();
    return;
  }
  if(name.length>MAX_PROFILE_NAME_LENGTH){
    profileNameError.textContent=`Profile names must be ${MAX_PROFILE_NAME_LENGTH} characters or fewer.`;
    profileNameInput.setAttribute("aria-invalid","true");
    profileNameInput.focus();
    return;
  }

  const action=profileNameDialogAction;
  const profile=action?.action==="rename" ? findProfileById(action.profileId) : null;
  if(profileNameExists(name,profile?.id || "")){
    profileNameError.textContent=`A profile named “${name}” already exists.`;
    profileNameInput.setAttribute("aria-invalid","true");
    profileNameInput.focus();
    return;
  }

  const settings=getSelectedProfileSource()==="default" ? defaultSettings : getSettingsFromForm();
  const saved=action?.action==="rename" && profile
    ? renameProfile(profile,name)
    : createProfile(name,settings);
  if(saved) closeProfileNameDialog();
}

function deleteActiveProfile(){
  const profile=findProfileById(activeProfileId);
  if(!profile) return;
  if(profiles.length<=1){
    setProfileStatus("At least one profile must remain.","error");
    return;
  }
  openConfirmationDialog({
    title:"Delete Profile",
    message:`Delete the profile “${profile.name}”? This cannot be undone.`,
    confirmLabel:"Delete Profile",
    onConfirm:()=>{
      if(activeProfileId!==profile.id){
        setProfileStatus("The active profile changed. No profile was deleted.","error");
        return;
      }
      saveSettings();
      const previousProfiles=profiles;
      const previousActiveProfileId=activeProfileId;
      profiles=profiles.filter(item=>item.id!==profile.id);
      const nextProfile=[...profiles].sort((a,b)=>a.name.localeCompare(b.name,undefined,{ sensitivity:"base" }))[0];
      activeProfileId=nextProfile.id;
      if(!persistProfiles({deletedIds:[profile.id]})){
        profiles=previousProfiles;
        activeProfileId=previousActiveProfileId;
        setProfileStatus("This browser could not delete the profile.","error");
        return;
      }
      applySettings({
        ...nextProfile.settings,
        showAdvancedSettings:showAdvancedSettingsToggle.checked,
        darkMode:themeToggle.getAttribute("aria-pressed")==="true"
      });
      saveSettings();
      renderProfileOptions(nextProfile.id);
      setProfileStatus("");
    }
  });
}

function persistSettings(){
  const settings=normalizeSavedSettings(getSettingsFromForm());
  const activeProfile=findProfileById(activeProfileId);
  let previousSettings=null;
  let previousUpdatedAt=null;
  let previousSettingsRaw=null;
  if(activeProfile){
    previousSettings={...activeProfile.settings};
    previousUpdatedAt=activeProfile.updatedAt;
    activeProfile.settings=normalizeProfileSettings(settings);
    activeProfile.updatedAt=Date.now();
  }
  try{
    previousSettingsRaw=window.localStorage.getItem(SETTINGS_KEY);
    window.localStorage.setItem(SETTINGS_KEY,JSON.stringify(settings));
    if(activeProfile && !persistProfiles()) throw new Error("Failed to persist profile settings");
    return true;
  }catch(e){
    if(activeProfile){
      activeProfile.settings=previousSettings;
      activeProfile.updatedAt=previousUpdatedAt;
    }
    try{
      if(previousSettingsRaw===null) window.localStorage.removeItem(SETTINGS_KEY);
      else window.localStorage.setItem(SETTINGS_KEY,previousSettingsRaw);
    }catch(restoreError){}
    return false;
  }
}

function saveSettings(){
  if(settingsSaveTimerId!==null){
    clearTimeout(settingsSaveTimerId);
    settingsSaveTimerId=null;
  }
  return persistSettings();
}

function scheduleSettingsSave(){
  if(settingsSaveTimerId!==null){
    clearTimeout(settingsSaveTimerId);
  }
  settingsSaveTimerId=setTimeout(()=>{
    settingsSaveTimerId=null;
    persistSettings();
  },150);
}

function resetSettingsToDefault(){
  const activeProfile=findProfileById(activeProfileId);
  if(!activeProfile) return;
  const profileId=activeProfile.id;
  const profileName=activeProfile.name;
  openConfirmationDialog({
    title:"Reset Profile",
    message:`Reset “${profileName}” to default settings? This cannot be undone.`,
    confirmLabel:"Reset Profile",
    onConfirm:()=>{
      if(activeProfileId!==profileId){
        setProfileStatus("The active profile changed. No settings were reset.","error");
        return;
      }
      const currentProfile=findProfileById(profileId);
      if(!currentProfile) return;
      const previousSettings={...currentProfile.settings};
      const defaults={
        ...defaultSettings,
        darkMode:themeToggle.getAttribute("aria-pressed")==="true",
        showAdvancedSettings:showAdvancedSettingsToggle.checked
      };
      applySettings(defaults);
      if(!saveSettings()){
        currentProfile.settings=previousSettings;
        applySettings(previousSettings);
        setProfileStatus("This browser could not save the reset settings.","error");
        return;
      }
      setProfileStatus("");
    }
  });
}

function applyTheme(isDark){
  document.body.classList.toggle("theme-dark",isDark);
  chartInteractionState.forEach(state=>{
    state.colors=null;
    if(state.container && state.config && state.circles.length){
      state.colors=getChartThemeColors();
      applyChartState(state.container,state.config);
    }
  });
}

function formatPlaybackSpeed(value){
  const normalized=Math.max(1,Math.min(1.5,parseFloat(value)||1));
  return normalized.toFixed(1).replace(/\.0$/,"") + "x";
}

function formatBeepVolume(value){
  return normalizeBeepVolumeSetting(value).toFixed(0) + "%";
}

function updateThresholdLabels(){
  correctThresholdValue.textContent=correctThresholdInput.value;
  incorrectThresholdValue.textContent=incorrectThresholdInput.value;
}

function getIndicatorSlotCount(){
  const thresholds=getThresholds();
  return Math.max(thresholds.correct,thresholds.incorrect);
}

function applyArithmeticMode(mode){
  arithmeticMode=ARITHMETIC_MODES.has(mode) ? mode : defaultSettings.mode;
  modeSelect.value=arithmeticMode;
}

function applyAdvancedSettingsVisibility(isVisible){
  advancedSettingsPanel.classList.toggle("hidden",!isVisible);
  advancedSections.classList.toggle("hidden",!isVisible);
  modeField.classList.toggle("hidden",!isVisible);
  nBackLevelField.classList.toggle("hidden",!isVisible);
  if(!isVisible && thresholdHelp){
    thresholdHelp.classList.remove("tooltip-pinned");
  }
  if(!isVisible && nBackHelp){
    nBackHelp.classList.remove("tooltip-pinned");
  }
  syncThresholdInfoAria();
  syncNBackInfoAria();
}

function applySettings(settings){
  maximumIntervalInput.value=settings.maximumInterval;
  startingIntervalInput.value=settings.startingInterval;
  minimumIntervalInput.value=settings.minimumInterval;
  intervalIncrementSelect.value=settings.intervalIncrement;
  updateIntervalInputConstraints();
  rememberIntervalInputValue(startingIntervalInput);
  rememberIntervalInputValue(maximumIntervalInput);
  rememberIntervalInputValue(minimumIntervalInput);
  correctThresholdInput.value=settings.correctThreshold;
  incorrectThresholdInput.value=settings.incorrectThreshold;
  durationInput.value=settings.duration;
  endConditionSelect.value=settings.endCondition;
  targetCorrectInput.value=settings.targetCorrect;
  applyArithmeticMode(settings.mode);
  nBackLevel=normalizeNBackLevel(settings.nBackLevel);
  nBackLevelInput.value=String(nBackLevel);
  selectedVoice=resolveVoiceKey(settings.voice);
  voiceSelect.value=selectedVoice;
  playbackSpeedSelect.value=Math.max(1,Math.min(1.5,parseFloat(settings.playbackSpeed)||1));
  playbackSpeedValue.textContent=formatPlaybackSpeed(playbackSpeedSelect.value);
  beepVolumeSelect.value=normalizeBeepVolumeSetting(settings.beepVolume);
  beepVolumeValue.textContent=formatBeepVolume(beepVolumeSelect.value);
  beepVolume=normalizeBeepVolumeSetting(beepVolumeSelect.value);
  beepToggle.checked=settings.beepEnabled;
  if(Object.prototype.hasOwnProperty.call(settings,"darkMode")){
    themeToggle.setAttribute("aria-pressed",String(!!settings.darkMode));
    themeToggle.setAttribute("aria-label",settings.darkMode ? "Disable dark mode" : "Enable dark mode");
    themeToggle.title=settings.darkMode ? "Disable dark mode" : "Enable dark mode";
  }
  showIntervalTimingToggle.checked=settings.showIntervalTiming;
  hideTimerDuringSessionToggle.checked=settings.hideTimerDuringSession;
  intervalIncrementValue.textContent=settings.intervalIncrement;
  updateThresholdLabels();
  currentInterval.textContent=settings.startingInterval;
  if(Object.prototype.hasOwnProperty.call(settings,"darkMode")){
    applyTheme(!!settings.darkMode);
  }
  intervalIncrement=parseInt(intervalIncrementSelect.value)||parseInt(defaultSettings.intervalIncrement);
  playbackSpeed=parseFloat(playbackSpeedSelect.value)||1;
  showAdvancedSettingsToggle.checked=settings.showAdvancedSettings;
  applyAdvancedSettingsVisibility(settings.showAdvancedSettings);
  applyIntervalTimingVisibility(settings.showIntervalTiming);
  hideTimerDuringSession=hideTimerDuringSessionToggle.checked;
  updateEndConditionControls();
}

function handleSettingsChange(event){
  const target=event?.currentTarget || event?.target;

  if(target===themeToggle){
    applyTheme(themeToggle.getAttribute("aria-pressed")==="true");
  }else if(target===modeSelect){
    applyArithmeticMode(modeSelect.value);
  }else if(target===nBackLevelInput){
    nBackLevel=normalizeNBackLevel(nBackLevelInput.value);
    nBackLevelInput.value=String(nBackLevel);
  }else if(target===voiceSelect){
    selectedVoice=resolveVoiceKey(voiceSelect.value);
    voiceSelect.value=selectedVoice;
    if(sessionState==="active"){
      void preloadVoice(selectedVoice).then(()=>{
        if(sessionState==="active"){
          retainOnlyVoiceCache(selectedVoice);
        }
      }).catch(()=>{});
    }
  }else if(target===intervalIncrementSelect){
    intervalIncrement=parseInt(intervalIncrementSelect.value)||parseInt(defaultSettings.intervalIncrement);
    intervalIncrementValue.textContent=intervalIncrement;
    updateIntervalInputConstraints();
  }else if(target===correctThresholdInput || target===incorrectThresholdInput){
    updateThresholdLabels();
    updateFeedbackUI();
  }else if(target===playbackSpeedSelect){
    playbackSpeed=parseFloat(playbackSpeedSelect.value)||1;
    playbackSpeedValue.textContent=formatPlaybackSpeed(playbackSpeed);
  }else if(target===beepVolumeSelect){
    beepVolume=normalizeBeepVolumeSetting(beepVolumeSelect.value);
    beepVolumeValue.textContent=formatBeepVolume(beepVolume);
  }else if(target===showAdvancedSettingsToggle){
    applyAdvancedSettingsVisibility(showAdvancedSettingsToggle.checked);
  }else if(target===showIntervalTimingToggle){
    applyIntervalTimingVisibility(showIntervalTimingToggle.checked);
  }else if(target===hideTimerDuringSessionToggle){
    hideTimerDuringSession=hideTimerDuringSessionToggle.checked;
  }else if(target===endConditionSelect || target===beepToggle){
    updateEndConditionControls();
  }

  scheduleSettingsSave();
}

function applyIntervalTimingVisibility(isVisible){
  const wasVisible=showIntervalTiming;
  showIntervalTiming=isVisible;
  intervalStats.classList.toggle("hidden",!isVisible);
  if(resultsIntervalStatsWrap){
    resultsIntervalStatsWrap.classList.toggle("hidden",!isVisible);
  }
  if(!isVisible){
    if(intervalStatsTimerId!==null){
      clearTimeout(intervalStatsTimerId);
      intervalStatsTimerId=null;
    }
    if(wasVisible && gameRunning && currentIntervalStart){
      const now=getClockTime();
      if(interval !== startingInterval || intervalCounts[interval]){
        intervalTime[interval]=(intervalTime[interval]||0)+(now-currentIntervalStart);
      }
    }
    intervalStats.innerHTML="";
  }else if(gameRunning){
    currentIntervalStart=getClockTime();
  }
}

function updateEndConditionControls(){
  const isCorrectMode=endConditionSelect.value==="correct";
  const isBeepEnabled=beepToggle.checked;
  durationInput.disabled=isCorrectMode;
  targetCorrectInput.disabled=!isCorrectMode;
  beepVolumeSelect.disabled=!isBeepEnabled;
  durationField.classList.toggle("locked",isCorrectMode);
  targetCorrectField.classList.toggle("locked",!isCorrectMode);
  beepVolumeField.classList.toggle("locked",!isBeepEnabled);
  durationField.setAttribute("aria-disabled",isCorrectMode);
  targetCorrectField.setAttribute("aria-disabled",!isCorrectMode);
  beepVolumeField.setAttribute("aria-disabled",!isBeepEnabled);
}

function applyThresholdPreset(correct,incorrect){
  correctThresholdInput.value=String(correct);
  incorrectThresholdInput.value=String(incorrect);
  updateThresholdLabels();
  updateFeedbackUI();
  saveSettings();
}

function getExpectedAnswer(a,b){
  switch(arithmeticMode){
    case "multiplication":
      return a*b;
    case "subtraction":
      return a-b;
    case "difference":
      return Math.abs(a-b);
    case "addition":
    default:
      return a+b;
  }
}

const THRESHOLD_PRESETS={
  Balanced:{ correct:4, incorrect:4 },
  Strict:{ correct:5, incorrect:3 }
};

const HISTORY_FILTER_DEFS={
  status:{
    defaultValue:"all",
    values:new Set(["all","Completed","Manually exited"]),
    matches(session,value){
      return value==="all" || session.status===value;
    }
  },
  mode:{
    defaultValue:"all",
    values:new Set(["all","addition","multiplication","subtraction","difference"]),
    matches(session,value){
      return value==="all" || (session.arithmeticMode || defaultSettings.mode)===value;
    }
  },
  nBackLevel:{
    defaultValue:"all",
    values:new Set(["all","1","2","3","4","5"]),
    matches(session,value){
      return value==="all" || normalizeNBackLevel(session?.nBackLevel)===Number(value);
    }
  },
  trendInclusion:{
    defaultValue:"all",
    values:new Set(["all","included","excluded"]),
    matches(session,value){
      if(value==="all") return true;
      return value==="included" ? session.includeInTrends===true : session.includeInTrends===false;
    }
  }
};

function getActiveHistoryFilterCount(){
  return Object.entries(historyFilters).reduce((count,[key,value])=>{
    const def=HISTORY_FILTER_DEFS[key];
    return count + (def && value!==def.defaultValue ? 1 : 0);
  },0);
}

function applyHistoryFilters(sessions,filters=historyFilters){
  return sessions.filter(session=>matchesHistoryFilters(session,filters));
}

function matchesHistoryFilters(session,filters=historyFilters){
  return Object.entries(filters).every(([key,value])=>{
    const def=HISTORY_FILTER_DEFS[key];
    if(!def) return true;
    return def.matches(session,value);
  });
}

function setHistoryChartMode(mode){
  if(!ARITHMETIC_MODES.has(mode)) return;
  historyChartMode=mode;
  historyChartModeIsUserSelected=true;
  if(historyChartModeSelect){
    historyChartModeSelect.value=mode;
  }
}

function setHistoryChartNBackLevel(level){
  const resolvedLevel=normalizeNBackLevel(level);
  historyChartNBackLevel=resolvedLevel;
  historyChartNBackLevelIsUserSelected=true;
  if(historyChartNBackLevelSelect){
    historyChartNBackLevelSelect.value=String(resolvedLevel);
  }
}

function ensureHistoryChartMode(fallbackMode){
  const resolvedFallback=ARITHMETIC_MODES.has(fallbackMode) ? fallbackMode : defaultSettings.mode;
  if(!historyChartModeIsUserSelected || !ARITHMETIC_MODES.has(historyChartMode)){
    historyChartMode=resolvedFallback;
  }
  const resolvedMode=ARITHMETIC_MODES.has(historyChartMode) ? historyChartMode : resolvedFallback;
  if(historyChartModeSelect){
    historyChartModeSelect.value=resolvedMode;
  }
  return resolvedMode;
}

function ensureHistoryChartNBackLevel(fallbackLevel){
  const resolvedFallback=normalizeNBackLevel(fallbackLevel);
  if(!historyChartNBackLevelIsUserSelected || historyChartNBackLevel===null){
    historyChartNBackLevel=resolvedFallback;
  }
  const resolvedLevel=normalizeNBackLevel(historyChartNBackLevel,resolvedFallback);
  if(historyChartNBackLevelSelect){
    historyChartNBackLevelSelect.value=String(resolvedLevel);
  }
  return resolvedLevel;
}

function ensureHistoryChartSelection(fallbackMode,fallbackNBackLevel){
  const resolvedMode=ensureHistoryChartMode(fallbackMode);
  const resolvedNBackLevel=ensureHistoryChartNBackLevel(fallbackNBackLevel);
  if(historyChartModeNote){
    historyChartModeNote.textContent=`Charts show ${formatArithmeticModeLabel(resolvedMode)} · ${formatNBackLevel(resolvedNBackLevel)} sessions only.`;
  }
  return { mode:resolvedMode, nBackLevel:resolvedNBackLevel };
}

function syncHistoryFilterControls(){
  historyStatusFilter.value=historyFilters.status;
  historyModeFilter.value=historyFilters.mode;
  historyNBackFilter.value=historyFilters.nBackLevel;
  historyTrendFilter.value=historyFilters.trendInclusion;
  historyFilterBtn.setAttribute("aria-expanded",String(historyFilterVisible));
  const activeFilterCount=getActiveHistoryFilterCount();
  if(historyFilterCountBadge){
    historyFilterCountBadge.textContent=String(activeFilterCount);
    historyFilterCountBadge.classList.toggle("hidden",activeFilterCount===0);
  }
}

function setHistoryFilterValue(key,value){
  if(!(key in historyFilters)) return;
  const def=HISTORY_FILTER_DEFS[key];
  const nextValue=def && def.values && def.values.has(value) ? value : def.defaultValue;
  historyFilters[key]=nextValue;
  historyPageIndex=0;
  syncHistoryFilterControls();
}

function resetHistoryFilters(){
  Object.entries(HISTORY_FILTER_DEFS).forEach(([key,def])=>{
    historyFilters[key]=def.defaultValue;
  });
  historyPageIndex=0;
  syncHistoryFilterControls();
}

function setHistoryPageIndex(pageIndex){
  historyPageIndex=Math.max(0,Math.floor(Number(pageIndex)||0));
}

function createEmptyHistoryPageData(){
  return {
    sessions:[],
    totalSessions:0,
    pageIndex:0,
    pageCount:0,
    pageSize:HISTORY_PAGE_SIZE,
    visibleStart:0,
    visibleEnd:0,
    hasPrevious:false,
    hasNext:false
  };
}

function createEmptyTrendData(){
  return {
    accuracyPoints:[],
    responsePoints:[]
  };
}

function toggleHistoryFiltersVisible(forceVisible){
  historyFilterVisible=typeof forceVisible==="boolean" ? forceVisible : !historyFilterVisible;
  historyFiltersPanel.classList.toggle("hidden",!historyFilterVisible);
  historyFilterBtn.setAttribute("aria-expanded",String(historyFilterVisible));
}

function getThresholdPresetName(correct,incorrect){
  const match=Object.entries(THRESHOLD_PRESETS).find(([,preset])=>preset.correct===correct && preset.incorrect===incorrect);
  return match?match[0]:"";
}

function formatThresholdSummary(correct,incorrect){
  const presetName=getThresholdPresetName(correct,incorrect);
  if(presetName) return presetName;
  return "Custom (" + correct + " / " + incorrect + ")";
}

function formatArithmeticModeLabel(mode){
  switch(mode){
    case "multiplication":
      return "Multiplication";
    case "subtraction":
      return "Subtraction";
    case "difference":
      return "Difference";
    case "addition":
    default:
      return "Addition";
  }
}

function formatNBackLevel(value){
  return normalizeNBackLevel(value) + "-back";
}

function getDefaultTrendInclusion(status){
  return status==="Manually exited" ? false : true;
}

function generateSessionId(){
  if(window.crypto && typeof window.crypto.randomUUID==="function"){
    return window.crypto.randomUUID();
  }
  return "session_" + Date.now() + "_" + Math.random().toString(36).slice(2,10);
}

function txDone(tx){
  return new Promise((resolve,reject)=>{
    tx.oncomplete=()=>resolve();
    tx.onabort=()=>reject(tx.error || new Error("IndexedDB transaction aborted"));
    tx.onerror=()=>reject(tx.error || new Error("IndexedDB transaction failed"));
  });
}

function requestToPromise(request,errorMessage){
  return new Promise((resolve,reject)=>{
    request.onsuccess=()=>resolve(request.result);
    request.onerror=()=>reject(request.error || new Error(errorMessage));
  });
}

function normalizeHistoryRecord(record){
  const startedAt=Number(record?.startedAt)||Number(record?.endedAt)||Date.now();
  const endedAt=Number(record?.endedAt)||startedAt;
  const durationMs=Number(record?.durationMs);
  const correctAnswers=Number(record?.correctAnswers)||0;
  const totalQuestionsAsked=Number(record?.totalQuestionsAsked)||0;
  const averageResponseTimeMs=Number(record?.averageResponseTimeMs)||0;
  const medianResponseTimeMs=normalizeOptionalNonNegativeNumber(record?.medianResponseTimeMs);
  const responseTimeIqrMs=normalizeOptionalNonNegativeNumber(record?.responseTimeIqrMs);
  const rawCorrectThreshold=record?.correctThreshold ?? record?.thresholds?.correct;
  const rawIncorrectThreshold=record?.incorrectThreshold ?? record?.thresholds?.incorrect;
  const rawMode=record?.arithmeticMode ?? record?.mode;
  const rawNBackLevel=record?.nBackLevel ?? record?.nbackLevel;
  const status=record?.status==="Manually exited" ? "Manually exited" : "Completed";
  const correctThreshold=coercePositiveNumber(rawCorrectThreshold,defaultSettings.correctThreshold);
  const incorrectThreshold=coercePositiveNumber(rawIncorrectThreshold,defaultSettings.incorrectThreshold);
  const accuracy=Number.isFinite(record?.accuracy)
    ? Number(record.accuracy)
    : (totalQuestionsAsked?correctAnswers/totalQuestionsAsked*100:0);
  const rawIncludeInTrends=record?.includeInTrends;
  const includeInTrends=typeof rawIncludeInTrends==="boolean"
    ? rawIncludeInTrends
    : getDefaultTrendInclusion(status);

  const startingInterval=Math.max(100,Number(record?.startingInterval)||parseInt(defaultSettings.startingInterval));
  const maximumInterval=Math.max(startingInterval,Math.min(3000,Number(record?.maximumInterval)||startingInterval));

  return {
    ...record,
    schemaVersion:2,
    sessionId:record?.sessionId || generateSessionId(),
    startedAt,
    endedAt,
    status,
    arithmeticMode:ARITHMETIC_MODES.has(rawMode) ? rawMode : defaultSettings.mode,
    nBackLevel:normalizeNBackLevel(rawNBackLevel),
    endCondition:record?.endCondition || defaultSettings.endCondition,
    durationMs:Number.isFinite(durationMs) ? Math.max(0,durationMs) : Math.max(0,endedAt-startedAt),
    accuracy,
    correctAnswers,
    totalQuestionsAsked,
    averageResponseTimeMs,
    medianResponseTimeMs,
    responseTimeIqrMs,
    correctThreshold,
    incorrectThreshold,
    startingInterval,
    maximumInterval,
    minimumInterval:Math.max(100,Number(record?.minimumInterval)||parseInt(defaultSettings.minimumInterval)),
    intervalIncrement:Math.max(10,Number(record?.intervalIncrement)||parseInt(defaultSettings.intervalIncrement)),
    voice:resolveVoiceKey(record?.voice,defaultSettings.voice),
    playbackSpeed:Math.max(1,Math.min(1.5,Number(record?.playbackSpeed)||parseFloat(defaultSettings.playbackSpeed))),
    includeInTrends,
    thresholds:{
      correct:correctThreshold,
      incorrect:incorrectThreshold
    }
  };
}

function normalizeLatestTraceRecord(record){
  const trace=Array.isArray(record?.trace) ? record.trace : [];
  const normalizedTrace=trace
    .map((point,index)=>({
      questionNumber:Math.max(1,Number(point?.questionNumber)||index+1),
      interval:Math.max(1,Number(point?.interval)||0),
      timestamp:Number(point?.timestamp)||Number(record?.startedAt)||Date.now(),
      responseTime:point?.responseTime===null || point?.responseTime===undefined
        ? null
        : (Number.isFinite(Number(point?.responseTime)) ? Math.max(0,Number(point?.responseTime)) : null)
    }))
    .filter(point=>Number.isFinite(point.questionNumber) && Number.isFinite(point.interval));

  return {
    ...record,
    schemaVersion:1,
    id:"latest",
    sessionId:record?.sessionId || null,
    startedAt:Number(record?.startedAt)||Date.now(),
    endedAt:Number(record?.endedAt)||Number(record?.startedAt)||Date.now(),
    status:record?.status==="Manually exited" ? "Manually exited" : "Completed",
    totalQuestionsAsked:Math.max(0,Number(record?.totalQuestionsAsked)||0),
    nBackLevel:normalizeNBackLevel(record?.nBackLevel),
    trace:normalizedTrace
  };
}

function getTrendBucketId(dayKey,mode,nBackLevel){
  return [dayKey,mode,normalizeNBackLevel(nBackLevel)].join("|");
}

function normalizeTrendBucket(record){
  const mode=ARITHMETIC_MODES.has(record?.mode) ? record.mode : defaultSettings.mode;
  const nBackLevel=normalizeNBackLevel(record?.nBackLevel);
  const dayKey=String(record?.dayKey||"");
  const dayStart=Number(record?.dayStart);
  if(!dayKey || !Number.isFinite(dayStart)) return null;
  return {
    id:getTrendBucketId(dayKey,mode,nBackLevel),
    schemaVersion:1,
    dayKey,
    dayStart,
    mode,
    nBackLevel,
    accuracyTotal:Math.max(0,Number(record?.accuracyTotal)||0),
    accuracyWeightTotal:Math.max(0,Number(record?.accuracyWeightTotal)||0),
    accuracyCount:Math.max(0,Number(record?.accuracyCount)||0),
    responseTotal:Math.max(0,Number(record?.responseTotal)||0),
    responseWeightTotal:Math.max(0,Number(record?.responseWeightTotal)||0),
    responseCount:Math.max(0,Number(record?.responseCount)||0)
  };
}

function getTrendBucketContribution(session){
  if(!isTrendEligibleSession(session)) return null;
  const mode=ARITHMETIC_MODES.has(session?.arithmeticMode) ? session.arithmeticMode : defaultSettings.mode;
  const nBackLevel=normalizeNBackLevel(session?.nBackLevel);
  const timestamp=Number(session?.endedAt||session?.startedAt||Date.now());
  const date=new Date(timestamp);
  const dayKey=[
    date.getFullYear(),
    String(date.getMonth()+1).padStart(2,"0"),
    String(date.getDate()).padStart(2,"0")
  ].join("-");
  const weight=Math.max(1,Number(session?.totalQuestionsAsked)||0);
  const accuracy=Number(session?.accuracy);
  const responseTime=Number(session?.averageResponseTimeMs);
  return {
    id:getTrendBucketId(dayKey,mode,nBackLevel),
    schemaVersion:1,
    dayKey,
    dayStart:new Date(date.getFullYear(),date.getMonth(),date.getDate()).getTime(),
    mode,
    nBackLevel,
    accuracyTotal:Number.isFinite(accuracy) ? accuracy*weight : 0,
    accuracyWeightTotal:Number.isFinite(accuracy) ? weight : 0,
    accuracyCount:Number.isFinite(accuracy) ? 1 : 0,
    responseTotal:Number.isFinite(responseTime) ? responseTime*weight : 0,
    responseWeightTotal:Number.isFinite(responseTime) ? weight : 0,
    responseCount:Number.isFinite(responseTime) ? 1 : 0
  };
}

function applyTrendBucketContribution(buckets,contribution,factor){
  if(!contribution) return;
  const current=buckets.get(contribution.id) || {
    id:contribution.id,
    schemaVersion:1,
    dayKey:contribution.dayKey,
    dayStart:contribution.dayStart,
    mode:contribution.mode,
    nBackLevel:contribution.nBackLevel,
    accuracyTotal:0,
    accuracyWeightTotal:0,
    accuracyCount:0,
    responseTotal:0,
    responseWeightTotal:0,
    responseCount:0
  };
  if(!current) return;
  current.accuracyTotal=Math.max(0,current.accuracyTotal + factor*contribution.accuracyTotal);
  current.accuracyWeightTotal=Math.max(0,current.accuracyWeightTotal + factor*contribution.accuracyWeightTotal);
  current.accuracyCount=Math.max(0,current.accuracyCount + factor*contribution.accuracyCount);
  current.responseTotal=Math.max(0,current.responseTotal + factor*contribution.responseTotal);
  current.responseWeightTotal=Math.max(0,current.responseWeightTotal + factor*contribution.responseWeightTotal);
  current.responseCount=Math.max(0,current.responseCount + factor*contribution.responseCount);
  if(current.accuracyWeightTotal || current.responseWeightTotal){
    buckets.set(current.id,current);
  }else{
    buckets.delete(current.id);
  }
}

function subtractTrendBucketContribution(bucket,contribution){
  const normalized=normalizeTrendBucket(bucket);
  if(!normalized || !contribution) return normalized;
  return {
    ...normalized,
    accuracyTotal:Math.max(0,normalized.accuracyTotal-contribution.accuracyTotal),
    accuracyWeightTotal:Math.max(0,normalized.accuracyWeightTotal-contribution.accuracyWeightTotal),
    accuracyCount:Math.max(0,normalized.accuracyCount-contribution.accuracyCount),
    responseTotal:Math.max(0,normalized.responseTotal-contribution.responseTotal),
    responseWeightTotal:Math.max(0,normalized.responseWeightTotal-contribution.responseWeightTotal),
    responseCount:Math.max(0,normalized.responseCount-contribution.responseCount)
  };
}

function buildTrendBucketsFromSessions(sessions){
  const buckets=new Map();
  (Array.isArray(sessions) ? sessions : []).forEach(session=>{
    applyTrendBucketContribution(buckets,getTrendBucketContribution(session),1);
  });
  return [...buckets.values()];
}

function buildTrendDataFromBuckets(buckets,mode,nBackLevel){
  const resolvedMode=ARITHMETIC_MODES.has(mode) ? mode : defaultSettings.mode;
  const resolvedNBackLevel=normalizeNBackLevel(nBackLevel);
  const accuracyBuckets=new Map();
  const responseBuckets=new Map();
  (Array.isArray(buckets) ? buckets : []).forEach(rawBucket=>{
    const bucket=normalizeTrendBucket(rawBucket);
    if(!bucket || bucket.mode!==resolvedMode || bucket.nBackLevel!==resolvedNBackLevel) return;
    if(bucket.accuracyWeightTotal){
      accuracyBuckets.set(bucket.dayKey,{
        dayKey:bucket.dayKey,
        dayStart:bucket.dayStart,
        total:bucket.accuracyTotal,
        weightTotal:bucket.accuracyWeightTotal,
        count:bucket.accuracyCount
      });
    }
    if(bucket.responseWeightTotal){
      responseBuckets.set(bucket.dayKey,{
        dayKey:bucket.dayKey,
        dayStart:bucket.dayStart,
        total:bucket.responseTotal,
        weightTotal:bucket.responseWeightTotal,
        count:bucket.responseCount
      });
    }
  });
  return {
    accuracyPoints:finalizeDailyTrendBuckets(accuracyBuckets),
    responsePoints:finalizeDailyTrendBuckets(responseBuckets),
    mode:resolvedMode,
    nBackLevel:resolvedNBackLevel
  };
}

const sessionHistoryStore=(()=>{
  const DB_NAME="cct-session-history";
  const DB_VERSION=6;
  const STORE_NAME="sessions";
  const TRACE_STORE_NAME="latestTrace";
  const TOTALS_STORE_NAME="historyTotals";
  const TREND_STORE_NAME="trendBuckets";
  const TREND_META_ID="__meta__";
  const TREND_SCHEMA_VERSION=2;
  const ENDED_AT_INDEX_NAME="endedAt";
  const IMPORT_LEDGER_KEY="cct-session-history-imports";
  const fallbackSessions=[];
  const fallbackTrendBuckets=[];
  let fallbackLatestTrace=null;
  let trendBucketsInitialized=false;
  let fallbackTotals={
    completedSessions:0,
    totalCorrectAnswers:0,
    totalDurationMs:0
  };
  const HISTORY_BACKUP_KEY="cct-session-history-backup";
  let hasBackupSnapshot=false;
  let backupMigrationPromise=null;
  let trendInitializationPromise=null;
  let historyWriteChain=Promise.resolve();
  let dbPromise=null;
  const supportsIndexedDB=typeof window.indexedDB!=="undefined";

  function enqueueHistoryWrite(operation){
    const queued=historyWriteChain.then(operation,operation);
    historyWriteChain=queued.catch(()=>{});
    return queued;
  }

  function loadBackupSnapshot(){
    try{
      const saved=window.localStorage.getItem(HISTORY_BACKUP_KEY);
      if(!saved) return null;
      const parsed=JSON.parse(saved);
      return {
        sessions:Array.isArray(parsed?.sessions) ? parsed.sessions.map(normalizeHistoryRecord) : [],
        trendBuckets:Array.isArray(parsed?.trendBuckets) ? parsed.trendBuckets.map(normalizeTrendBucket).filter(Boolean) : null,
        latestTrace:parsed?.latestSessionTrace ? normalizeLatestTraceRecord(parsed.latestSessionTrace) : null,
        totals:parsed?.historyTotals ? normalizeTotalsRecord(parsed.historyTotals) : createEmptyTotals()
      };
    }catch(e){
      return null;
    }
  }

  function hasImportedBackup(importKey){
    if(!importKey) return false;
    try{
      const raw=window.localStorage.getItem(IMPORT_LEDGER_KEY);
      const keys=raw ? JSON.parse(raw) : [];
      return Array.isArray(keys) && keys.includes(importKey);
    }catch(e){
      return false;
    }
  }

  function rememberImportedBackup(importKey){
    if(!importKey) return;
    try{
      const raw=window.localStorage.getItem(IMPORT_LEDGER_KEY);
      const parsed=raw ? JSON.parse(raw) : [];
      const keys=Array.isArray(parsed) ? parsed : [];
      const next=[...new Set([...keys,importKey])].slice(-25);
      window.localStorage.setItem(IMPORT_LEDGER_KEY,JSON.stringify(next));
    }catch(e){}
  }

  function clearImportedBackupLedger(){
    try{
      window.localStorage.removeItem(IMPORT_LEDGER_KEY);
    }catch(e){}
  }

  function persistBackupSnapshot(){
    try{
      const snapshot={
        schemaVersion:2,
        exportedAt:new Date().toISOString(),
        sessions:fallbackSessions.map(normalizeHistoryRecord),
        trendBuckets:trendBucketsInitialized
          ? fallbackTrendBuckets.map(normalizeTrendBucket).filter(Boolean)
          : undefined,
        latestSessionTrace:fallbackLatestTrace ? normalizeLatestTraceRecord(fallbackLatestTrace) : null,
        historyTotals:normalizeTotalsRecord(fallbackTotals)
      };
      window.localStorage.setItem(HISTORY_BACKUP_KEY,JSON.stringify(snapshot));
    }catch(e){}
  }

  const initialBackup=loadBackupSnapshot();
  if(initialBackup){
    fallbackSessions.push(...initialBackup.sessions);
    if(initialBackup.trendBuckets){
      fallbackTrendBuckets.push(...initialBackup.trendBuckets);
      trendBucketsInitialized=true;
    }
    fallbackLatestTrace=initialBackup.latestTrace;
    fallbackTotals=initialBackup.totals;
    hasBackupSnapshot=!supportsIndexedDB;
  }

  async function migrateBackupSnapshotToIndexedDb(){
    if(!supportsIndexedDB || !hasBackupSnapshot) return;
    if(backupMigrationPromise) return backupMigrationPromise;

    backupMigrationPromise=(async()=>{
      try{
        const db=await openDb();
        if(!trendBucketsInitialized){
          fallbackTrendBuckets.push(...buildTrendBucketsFromSessions(fallbackSessions));
          trendBucketsInitialized=true;
        }
        const tx=db.transaction([STORE_NAME,TRACE_STORE_NAME,TOTALS_STORE_NAME,TREND_STORE_NAME],"readwrite");
        const sessionStore=tx.objectStore(STORE_NAME);
        fallbackSessions.forEach(session=>{
          sessionStore.put(normalizeHistoryRecord(session));
        });
        if(fallbackLatestTrace){
          tx.objectStore(TRACE_STORE_NAME).put(normalizeLatestTraceRecord(fallbackLatestTrace));
        }
        tx.objectStore(TOTALS_STORE_NAME).put(normalizeTotalsRecord(fallbackTotals));
        const trendStore=tx.objectStore(TREND_STORE_NAME);
        trendStore.clear();
        fallbackTrendBuckets.forEach(bucket=>trendStore.put(normalizeTrendBucket(bucket)));
        trendStore.put({id:TREND_META_ID,schemaVersion:TREND_SCHEMA_VERSION});
        await txDone(tx);
        hasBackupSnapshot=false;
      }catch(e){}
      backupMigrationPromise=null;
    })();

    return backupMigrationPromise;
  }

  function upsertFallbackSession(session){
    const index=fallbackSessions.findIndex(item=>item.sessionId===session.sessionId);
    if(index>=0){
      fallbackSessions[index]=session;
    }else{
      fallbackSessions.unshift(session);
    }
  }

  async function openDb(){
    if(!supportsIndexedDB) return null;
    if(dbPromise) return dbPromise;
    dbPromise=new Promise((resolve,reject)=>{
      const request=window.indexedDB.open(DB_NAME,DB_VERSION);

      request.onupgradeneeded=()=>{
        const db=request.result;
        if(!db.objectStoreNames.contains(STORE_NAME)){
          db.createObjectStore(STORE_NAME,{ keyPath:"sessionId" });
        }
        const sessionStore=request.transaction.objectStore(STORE_NAME);
        if(!sessionStore.indexNames.contains(ENDED_AT_INDEX_NAME)){
          sessionStore.createIndex(ENDED_AT_INDEX_NAME,"endedAt",{ unique:false });
        }
        if(!db.objectStoreNames.contains(TRACE_STORE_NAME)){
          db.createObjectStore(TRACE_STORE_NAME,{ keyPath:"id" });
        }
        if(!db.objectStoreNames.contains(TOTALS_STORE_NAME)){
          db.createObjectStore(TOTALS_STORE_NAME,{ keyPath:"id" });
        }
        if(!db.objectStoreNames.contains(TREND_STORE_NAME)){
          db.createObjectStore(TREND_STORE_NAME,{ keyPath:"id" });
        }
      };

      request.onsuccess=()=>resolve(request.result);
      request.onerror=()=>reject(request.error || new Error("Failed to open IndexedDB"));
    });
    return dbPromise;
  }

  async function readTrendBucketsFromDb(){
    if(!supportsIndexedDB){
      return fallbackTrendBuckets.map(normalizeTrendBucket).filter(Boolean);
    }
    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      return fallbackTrendBuckets.map(normalizeTrendBucket).filter(Boolean);
    }
    try{
      const db=await openDb();
      const tx=db.transaction(TREND_STORE_NAME,"readonly");
      const records=await requestToPromise(
        tx.objectStore(TREND_STORE_NAME).getAll(),
        "Failed to read trend data"
      );
      return records.map(normalizeTrendBucket).filter(Boolean);
    }catch(e){
      return fallbackTrendBuckets.map(normalizeTrendBucket).filter(Boolean);
    }
  }

  async function writeTrendBucketsToDb(buckets,deletedIds=[]){
    const normalizedBuckets=buckets.map(normalizeTrendBucket).filter(Boolean);
    if(!supportsIndexedDB || hasBackupSnapshot){
      fallbackTrendBuckets.length=0;
      fallbackTrendBuckets.push(...normalizedBuckets);
      trendBucketsInitialized=true;
      persistBackupSnapshot();
      return;
    }
    {
      const db=await openDb();
      const tx=db.transaction(TREND_STORE_NAME,"readwrite");
      const store=tx.objectStore(TREND_STORE_NAME);
      deletedIds.forEach(id=>store.delete(id));
      normalizedBuckets.forEach(bucket=>store.put(bucket));
      store.put({id:TREND_META_ID,schemaVersion:TREND_SCHEMA_VERSION});
      await txDone(tx);
      fallbackTrendBuckets.length=0;
      fallbackTrendBuckets.push(...normalizedBuckets);
      trendBucketsInitialized=true;
      persistBackupSnapshot();
    }
  }

  async function ensureTrendBuckets(){
    if(trendBucketsInitialized) return;
    if(trendInitializationPromise) return trendInitializationPromise;
    trendInitializationPromise=(async()=>{
      if(!supportsIndexedDB){
        fallbackTrendBuckets.length=0;
        fallbackTrendBuckets.push(...buildTrendBucketsFromSessions(fallbackSessions));
        trendBucketsInitialized=true;
        persistBackupSnapshot();
        return;
      }

      await migrateBackupSnapshotToIndexedDb();
      if(hasBackupSnapshot) return;
      const db=await openDb();
      const tx=db.transaction(TREND_STORE_NAME,"readonly");
      const records=await requestToPromise(
        tx.objectStore(TREND_STORE_NAME).getAll(),
        "Failed to read trend metadata"
      );
      const metadata=records.find(record=>record?.id===TREND_META_ID);
      if(Number(metadata?.schemaVersion)>=TREND_SCHEMA_VERSION){
        fallbackTrendBuckets.length=0;
        fallbackTrendBuckets.push(...records.map(normalizeTrendBucket).filter(Boolean));
        trendBucketsInitialized=true;
        persistBackupSnapshot();
        return;
      }
      const sessionTx=db.transaction(STORE_NAME,"readonly");
      const stored=await requestToPromise(
        sessionTx.objectStore(STORE_NAME).getAll(),
        "Failed to read sessions for trend migration"
      );
      const rebuiltBuckets=buildTrendBucketsFromSessions(stored.map(normalizeHistoryRecord));
      const rebuiltIds=new Set(rebuiltBuckets.map(bucket=>bucket.id));
      const preservedBuckets=records
        .map(normalizeTrendBucket)
        .filter(bucket=>bucket && !rebuiltIds.has(bucket.id));
      await writeTrendBucketsToDb([...rebuiltBuckets,...preservedBuckets]);
    })();
    try{
      await trendInitializationPromise;
    }finally{
      trendInitializationPromise=null;
    }
  }

  async function updateTrendBucketsNow(previousSession,nextSession){
    await ensureTrendBuckets();
    const previousContribution=getTrendBucketContribution(previousSession);
    const nextContribution=getTrendBucketContribution(nextSession);
    const buckets=new Map((await readTrendBucketsFromDb()).map(bucket=>[bucket.id,bucket]));
    applyTrendBucketContribution(buckets,previousContribution,-1);
    applyTrendBucketContribution(buckets,nextContribution,1);
    await writeTrendBucketsToDb([...buckets.values()]);
  }

  function buildMergedTrendBuckets(currentBuckets,sessions,previousSessions,importedTrendBuckets){
    const buckets=new Map(currentBuckets.map(bucket=>[bucket.id,bucket]));
    const existingIds=new Set(buckets.keys());
    if(Array.isArray(importedTrendBuckets)){
      sessions.forEach(session=>{
        const previousContribution=getTrendBucketContribution(previousSessions.get(session.sessionId));
        const nextContribution=getTrendBucketContribution(session);
        applyTrendBucketContribution(buckets,previousContribution,-1);
        applyTrendBucketContribution(buckets,nextContribution,1);
      });
      const importedSessionBuckets=new Map(buildTrendBucketsFromSessions(sessions).map(bucket=>[bucket.id,bucket]));
      importedTrendBuckets.forEach(bucket=>{
        const residual=subtractTrendBucketContribution(bucket,importedSessionBuckets.get(bucket.id));
        if(residual && (residual.accuracyWeightTotal || residual.responseWeightTotal)){
          applyTrendBucketContribution(buckets,residual,1);
        }
      });
    }else{
      sessions.forEach(session=>{
        const previousSession=previousSessions.get(session.sessionId);
        applyTrendBucketContribution(buckets,getTrendBucketContribution(previousSession),-1);
        applyTrendBucketContribution(buckets,getTrendBucketContribution(session),1);
      });
    }
    const deletedIds=[...existingIds].filter(id=>!buckets.has(id));
    return { buckets:[...buckets.values()], deletedIds };
  }

  async function mergeImportedTrendDataNow(sessions,previousSessions,importedTrendBuckets){
    await ensureTrendBuckets();
    const currentBuckets=await readTrendBucketsFromDb();
    const merged=buildMergedTrendBuckets(currentBuckets,sessions,previousSessions,importedTrendBuckets);
    await writeTrendBucketsToDb(merged.buckets,merged.deletedIds);
  }

  async function saveSessionInternal(record){
    const normalized=normalizeHistoryRecord(record);
    await ensureTrendBuckets();
    if(!supportsIndexedDB){
      const previousSession=fallbackSessions.find(session=>session.sessionId===normalized.sessionId) || null;
      const previousDelta=previousSession ? getSessionTotalsDelta(previousSession) : null;
      const nextDelta=getSessionTotalsDelta(normalized);
      upsertFallbackSession(normalized);
      if(previousDelta){
        fallbackTotals=subtractTotals(fallbackTotals,previousDelta);
      }
      fallbackTotals=addTotals(fallbackTotals,nextDelta);
      await updateTrendBucketsNow(previousSession,normalized);
      persistBackupSnapshot();
      return normalized;
    }

    const db=await openDb();
    const tx=db.transaction([STORE_NAME,TOTALS_STORE_NAME,TREND_STORE_NAME],"readwrite");
    const sessionStore=tx.objectStore(STORE_NAME);
    const trendStore=tx.objectStore(TREND_STORE_NAME);
    const previousRaw=await requestToPromise(
      sessionStore.get(normalized.sessionId),
      "Failed to read session before saving"
    );
    const previousSession=previousRaw ? normalizeHistoryRecord(previousRaw) : null;
    const previousDelta=previousSession ? getSessionTotalsDelta(previousSession) : null;
    const nextDelta=getSessionTotalsDelta(normalized);
    const currentTotals=normalizeTotalsRecord(await requestToPromise(
      tx.objectStore(TOTALS_STORE_NAME).get("totals"),
      "Failed to read history totals before saving"
    ));
    const updatedTotals=addTotals(previousDelta ? subtractTotals(currentTotals,previousDelta) : currentTotals,nextDelta);
    const previousContribution=getTrendBucketContribution(previousSession);
    const nextContribution=getTrendBucketContribution(normalized);
    const bucketIds=[...new Set([previousContribution,nextContribution].filter(Boolean).map(contribution=>contribution.id))];
    const buckets=new Map();
    await Promise.all(bucketIds.map(async id=>{
      const bucket=normalizeTrendBucket(await requestToPromise(
        trendStore.get(id),
        "Failed to read trend bucket before saving"
      ));
      if(bucket) buckets.set(id,bucket);
    }));
    applyTrendBucketContribution(buckets,previousContribution,-1);
    applyTrendBucketContribution(buckets,nextContribution,1);
    sessionStore.put(normalized);
    tx.objectStore(TOTALS_STORE_NAME).put(updatedTotals);
    bucketIds.forEach(id=>{
      const bucket=buckets.get(id);
      if(bucket) trendStore.put(bucket);
      else trendStore.delete(id);
    });
    trendStore.put({id:TREND_META_ID,schemaVersion:TREND_SCHEMA_VERSION});
    await txDone(tx);
    upsertFallbackSession(normalized);
    fallbackTotals=updatedTotals;
    fallbackTrendBuckets.length=0;
    fallbackTrendBuckets.push(...(await readTrendBucketsFromDb()));
    persistBackupSnapshot();
    return normalized;
  }

  function saveSession(record){
    return enqueueHistoryWrite(()=>saveSessionInternal(record));
  }

  function getSortedFallbackSessions(){
    return fallbackSessions
      .map(normalizeHistoryRecord)
      .sort((a,b)=>Number(b.endedAt||0)-Number(a.endedAt||0));
  }

  function buildPagedSessionResult(sessions,pageIndex,pageSize){
    const totalSessions=sessions.length;
    const pageCount=totalSessions ? Math.ceil(totalSessions/pageSize) : 0;
    const resolvedPageIndex=pageCount ? Math.min(pageIndex,pageCount-1) : 0;
    const startIndex=pageCount ? resolvedPageIndex*pageSize : 0;
    const pageSessions=pageCount ? sessions.slice(startIndex,startIndex+pageSize) : [];
    const visibleStart=pageSessions.length ? startIndex + 1 : 0;
    const visibleEnd=pageSessions.length ? startIndex + pageSessions.length : 0;

    return {
      sessions:pageSessions,
      totalSessions,
      pageIndex:resolvedPageIndex,
      pageCount,
      pageSize,
      visibleStart,
      visibleEnd,
      hasPrevious:resolvedPageIndex>0,
      hasNext:pageCount>0 && resolvedPageIndex<pageCount-1
    };
  }

  async function getSessionPage({ filters=historyFilters, pageIndex=0, pageSize=HISTORY_PAGE_SIZE }={}){
    const safePageSize=Math.max(1,Math.floor(Number(pageSize)||HISTORY_PAGE_SIZE));
    const requestedPageIndex=Math.max(0,Math.floor(Number(pageIndex)||0));

    if(!supportsIndexedDB){
      const filtered=applyHistoryFilters(getSortedFallbackSessions(),filters);
      return buildPagedSessionResult(filtered,requestedPageIndex,safePageSize);
    }

    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      const filtered=applyHistoryFilters(getSortedFallbackSessions(),filters);
      return buildPagedSessionResult(filtered,requestedPageIndex,safePageSize);
    }

    const readPagedSessions=async(pageIndexToUse)=>{
      const db=await openDb();
      const tx=db.transaction(STORE_NAME,"readonly");
      const source=tx.objectStore(STORE_NAME).index(ENDED_AT_INDEX_NAME);
      const pageStart=pageIndexToUse*safePageSize;
      const pageSessions=[];
      let totalSessions=0;

      await new Promise((resolve,reject)=>{
        const request=source.openCursor(null,"prev");
        request.onsuccess=()=>{
          const cursor=request.result;
          if(!cursor){
            resolve();
            return;
          }

          const session=normalizeHistoryRecord(cursor.value);
          if(matchesHistoryFilters(session,filters)){
            if(totalSessions>=pageStart && pageSessions.length<safePageSize){
              pageSessions.push(session);
            }
            totalSessions++;
          }
          cursor.continue();
        };
        request.onerror=()=>reject(request.error || new Error("Failed to read sessions"));
      });

      const pageCount=totalSessions ? Math.ceil(totalSessions/safePageSize) : 0;
      const visibleStart=pageSessions.length ? pageStart + 1 : 0;
      const visibleEnd=pageSessions.length ? pageStart + pageSessions.length : 0;

      return {
        sessions:pageSessions,
        totalSessions,
        pageIndex:pageIndexToUse,
        pageCount,
        pageSize:safePageSize,
        visibleStart,
        visibleEnd,
        hasPrevious:pageIndexToUse>0,
        hasNext:pageCount>0 && pageIndexToUse<pageCount-1
      };
    };

    try{
      const initialResult=await readPagedSessions(requestedPageIndex);
      if(initialResult.pageCount && initialResult.pageIndex>initialResult.pageCount-1){
        return readPagedSessions(initialResult.pageCount-1);
      }
      return initialResult;
    }catch(e){
      const filtered=applyHistoryFilters(getSortedFallbackSessions(),filters);
      return buildPagedSessionResult(filtered,requestedPageIndex,safePageSize);
    }
  }

  function getDefaultHistorySettings(){
    return {
      mode:defaultSettings.mode,
      nBackLevel:normalizeNBackLevel(defaultSettings.nBackLevel)
    };
  }

  function getMostRecentFallbackHistorySettings(){
    const latestSession=getSortedFallbackSessions().find(session=>ARITHMETIC_MODES.has(session?.arithmeticMode));
    if(latestSession){
      return {
        mode:latestSession.arithmeticMode,
        nBackLevel:normalizeNBackLevel(latestSession.nBackLevel)
      };
    }
    const latestTrend=fallbackTrendBuckets
      .filter(bucket=>ARITHMETIC_MODES.has(bucket?.mode))
      .sort((a,b)=>Number(b.dayStart||0)-Number(a.dayStart||0))[0];
    return latestTrend
      ? {
          mode:latestTrend.mode,
          nBackLevel:normalizeNBackLevel(latestTrend.nBackLevel)
        }
      : getDefaultHistorySettings();
  }

  async function getMostRecentHistorySettings(){
    if(!supportsIndexedDB){
      return getMostRecentFallbackHistorySettings();
    }

    await ensureTrendBuckets();
    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      return getMostRecentFallbackHistorySettings();
    }

    try{
      const db=await openDb();
      const tx=db.transaction(STORE_NAME,"readonly");
      const source=tx.objectStore(STORE_NAME).index(ENDED_AT_INDEX_NAME);
      const latestSession=await new Promise((resolve,reject)=>{
        const request=source.openCursor(null,"prev");
        request.onsuccess=()=>{
          const cursor=request.result;
          if(!cursor){
            resolve(null);
            return;
          }
          resolve(normalizeHistoryRecord(cursor.value));
        };
        request.onerror=()=>reject(request.error || new Error("Failed to read most recent session"));
      });
      if(latestSession && ARITHMETIC_MODES.has(latestSession.arithmeticMode)){
        return {
          mode:latestSession.arithmeticMode,
          nBackLevel:normalizeNBackLevel(latestSession.nBackLevel)
        };
      }
      const trendBuckets=await readTrendBucketsFromDb();
      const latestTrend=trendBuckets
        .filter(bucket=>ARITHMETIC_MODES.has(bucket?.mode))
        .sort((a,b)=>Number(b.dayStart||0)-Number(a.dayStart||0))[0];
      return latestTrend
        ? {
            mode:latestTrend.mode,
            nBackLevel:normalizeNBackLevel(latestTrend.nBackLevel)
          }
        : getDefaultHistorySettings();
    }catch(e){
      return getMostRecentFallbackHistorySettings();
    }
  }

  async function getTrendData(mode,nBackLevel){
    const resolvedMode=ARITHMETIC_MODES.has(mode) ? mode : defaultSettings.mode;
    const resolvedNBackLevel=normalizeNBackLevel(nBackLevel);
    try{
      await ensureTrendBuckets();
      return buildTrendDataFromBuckets(
        await readTrendBucketsFromDb(),
        resolvedMode,
        resolvedNBackLevel
      );
    }catch(e){
      return buildTrendDataForSessions(getSortedFallbackSessions(),resolvedMode,resolvedNBackLevel);
    }
  }

  async function saveLatestTraceInternal(record){
    const normalized=normalizeLatestTraceRecord(record);
    if(!supportsIndexedDB){
      fallbackLatestTrace=normalized;
      persistBackupSnapshot();
      return normalized;
    }

    const db=await openDb();
    const tx=db.transaction(TRACE_STORE_NAME,"readwrite");
    tx.objectStore(TRACE_STORE_NAME).put(normalized);
    await txDone(tx);
    fallbackLatestTrace=normalized;
    persistBackupSnapshot();
    return normalized;
  }

  function saveLatestTrace(record){
    return enqueueHistoryWrite(()=>saveLatestTraceInternal(record));
  }

  function createEmptyTotals(){
    return {
      id:"totals",
      schemaVersion:1,
      completedSessions:0,
      totalCorrectAnswers:0,
      totalDurationMs:0
    };
  }

  function normalizeTotalsRecord(record){
    const base=createEmptyTotals();
    if(!record) return base;
    return {
      ...base,
      ...record,
      id:"totals",
      schemaVersion:1,
      completedSessions:Math.max(0,Number(record.completedSessions)||0),
      totalCorrectAnswers:Math.max(0,Number(record.totalCorrectAnswers)||0),
      totalDurationMs:Math.max(0,Number(record.totalDurationMs)||0)
    };
  }

  function getSessionTotalsDelta(session){
    return {
      completedSessions:session?.status==="Completed" ? 1 : 0,
      totalCorrectAnswers:Number(session?.correctAnswers)||0,
      totalDurationMs:Number(session?.durationMs)||0
    };
  }

  function addTotals(base,delta){
    return normalizeTotalsRecord({
      ...base,
      completedSessions:(Number(base?.completedSessions)||0) + (Number(delta?.completedSessions)||0),
      totalCorrectAnswers:(Number(base?.totalCorrectAnswers)||0) + (Number(delta?.totalCorrectAnswers)||0),
      totalDurationMs:(Number(base?.totalDurationMs)||0) + (Number(delta?.totalDurationMs)||0)
    });
  }

  function subtractTotals(base,delta){
    return normalizeTotalsRecord({
      ...base,
      completedSessions:Math.max(0,(Number(base?.completedSessions)||0) - (Number(delta?.completedSessions)||0)),
      totalCorrectAnswers:Math.max(0,(Number(base?.totalCorrectAnswers)||0) - (Number(delta?.totalCorrectAnswers)||0)),
      totalDurationMs:Math.max(0,(Number(base?.totalDurationMs)||0) - (Number(delta?.totalDurationMs)||0))
    });
  }

  function sumSessionTotals(sessions){
    return (Array.isArray(sessions) ? sessions : [])
      .reduce((totals,session)=>addTotals(totals,getSessionTotalsDelta(session)),createEmptyTotals());
  }

  async function readStoredTotals(){
    if(!supportsIndexedDB){
      return normalizeTotalsRecord(fallbackTotals);
    }

    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      return normalizeTotalsRecord(fallbackTotals);
    }

    try{
      const db=await openDb();
      const tx=db.transaction(TOTALS_STORE_NAME,"readonly");
      const totals=await requestToPromise(
        tx.objectStore(TOTALS_STORE_NAME).get("totals"),
        "Failed to read history totals"
      );
      if(totals){
        fallbackTotals=normalizeTotalsRecord(totals);
        return fallbackTotals;
      }
    }catch(e){}

    return normalizeTotalsRecord(fallbackTotals);
  }

  async function getAllSessions(){
    if(!supportsIndexedDB){
      return getSortedFallbackSessions();
    }

    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      return getSortedFallbackSessions();
    }

    try{
      const db=await openDb();
      const tx=db.transaction(STORE_NAME,"readonly");
      const sessions=await requestToPromise(
        tx.objectStore(STORE_NAME).getAll(),
        "Failed to read history"
      );
      fallbackSessions.length=0;
      fallbackSessions.push(...sessions.map(normalizeHistoryRecord));
      return sessions.map(normalizeHistoryRecord).sort((a,b)=>b.endedAt-a.endedAt);
    }catch(e){
      return getSortedFallbackSessions();
    }
  }

  async function getLatestTrace(){
    if(!supportsIndexedDB){
      return fallbackLatestTrace ? normalizeLatestTraceRecord(fallbackLatestTrace) : null;
    }

    await migrateBackupSnapshotToIndexedDb();
    if(hasBackupSnapshot){
      return fallbackLatestTrace ? normalizeLatestTraceRecord(fallbackLatestTrace) : null;
    }

    try{
      const db=await openDb();
      const tx=db.transaction(TRACE_STORE_NAME,"readonly");
      const trace=await requestToPromise(
        tx.objectStore(TRACE_STORE_NAME).get("latest"),
        "Failed to read latest trace"
      );
      if(trace){
        fallbackLatestTrace=normalizeLatestTraceRecord(trace);
      }
      return trace ? normalizeLatestTraceRecord(trace) : null;
    }catch(e){
      return fallbackLatestTrace ? normalizeLatestTraceRecord(fallbackLatestTrace) : null;
    }
  }

  async function clearAllInternal(){
    if(!supportsIndexedDB){
      fallbackSessions.length=0;
      fallbackTrendBuckets.length=0;
      trendBucketsInitialized=true;
      fallbackLatestTrace=null;
      fallbackTotals=createEmptyTotals();
      persistBackupSnapshot();
      clearImportedBackupLedger();
      return;
    }

    const db=await openDb();
    const tx=db.transaction([STORE_NAME,TRACE_STORE_NAME,TOTALS_STORE_NAME,TREND_STORE_NAME],"readwrite");
    tx.objectStore(STORE_NAME).clear();
    tx.objectStore(TRACE_STORE_NAME).clear();
    tx.objectStore(TOTALS_STORE_NAME).clear();
    tx.objectStore(TREND_STORE_NAME).clear();
    await txDone(tx);
    fallbackSessions.length=0;
    fallbackTrendBuckets.length=0;
    trendBucketsInitialized=true;
    fallbackLatestTrace=null;
    fallbackTotals=createEmptyTotals();
    persistBackupSnapshot();
    clearImportedBackupLedger();
  }

  async function clearSessionsOnlyInternal(){
    await ensureTrendBuckets();
    if(!supportsIndexedDB){
      fallbackSessions.length=0;
      fallbackLatestTrace=null;
      persistBackupSnapshot();
      clearImportedBackupLedger();
      return;
    }

    const db=await openDb();
    const tx=db.transaction([STORE_NAME,TRACE_STORE_NAME,TREND_STORE_NAME],"readwrite");
    tx.objectStore(STORE_NAME).clear();
    tx.objectStore(TRACE_STORE_NAME).clear();
    await txDone(tx);
    fallbackSessions.length=0;
    fallbackLatestTrace=null;
    persistBackupSnapshot();
    clearImportedBackupLedger();
  }

  function clearAll(){
    return enqueueHistoryWrite(clearAllInternal);
  }

  function clearSessionsOnly(){
    return enqueueHistoryWrite(clearSessionsOnlyInternal);
  }

  async function importDataInternal(payload){
    const importKey=payload && !Array.isArray(payload) ? String(payload.exportedAt||"") : "";
    if(hasImportedBackup(importKey)) return 0;
    const source=Array.isArray(payload) ? payload : (Array.isArray(payload?.sessions) ? payload.sessions : []);
    const sessions=source.map(normalizeHistoryRecord);
    const importedTrendBuckets=Array.isArray(payload?.trendBuckets)
      ? payload.trendBuckets.map(normalizeTrendBucket).filter(Boolean)
      : null;
    const latestTracePayload=payload?.latestSessionTrace ?? payload?.latestTrace ?? null;
    const latestTrace=latestTracePayload ? normalizeLatestTraceRecord(latestTracePayload) : null;
    const totalsPayload=payload?.historyTotals ?? payload?.totals ?? null;
    const totals=totalsPayload ? normalizeTotalsRecord(totalsPayload) : null;
    await ensureTrendBuckets();

    if(!supportsIndexedDB){
      const existingSessions=new Map(fallbackSessions.map(session=>[session.sessionId,session]));
      const previousSessions=new Map(existingSessions);
      sessions.forEach(session=>{
        const previousSession=existingSessions.get(session.sessionId);
        upsertFallbackSession(session);
        existingSessions.set(session.sessionId,session);
        if(previousSession){
          fallbackTotals=subtractTotals(fallbackTotals,getSessionTotalsDelta(previousSession));
        }
        fallbackTotals=addTotals(fallbackTotals,getSessionTotalsDelta(session));
      });
      if(latestTrace) fallbackLatestTrace=latestTrace;
      if(totals){
        fallbackTotals=addTotals(
          fallbackTotals,
          subtractTotals(totals,sumSessionTotals(sessions))
        );
      }
      await mergeImportedTrendDataNow(sessions,previousSessions,importedTrendBuckets);
      persistBackupSnapshot();
      rememberImportedBackup(importKey);
      return sessions.length;
    }

    await ensureTrendBuckets();
    const db=await openDb();
    const tx=db.transaction([STORE_NAME,TRACE_STORE_NAME,TOTALS_STORE_NAME,TREND_STORE_NAME],"readwrite");
    const currentSessions=(await requestToPromise(
      tx.objectStore(STORE_NAME).getAll(),
      "Failed to read sessions before import"
    )).map(normalizeHistoryRecord);
    const currentBuckets=(await requestToPromise(
      tx.objectStore(TREND_STORE_NAME).getAll(),
      "Failed to read trends before import"
    )).map(normalizeTrendBucket).filter(Boolean);
    const currentTotals=normalizeTotalsRecord(await requestToPromise(
      tx.objectStore(TOTALS_STORE_NAME).get("totals"),
      "Failed to read totals before import"
    ));
    const currentSessionsById=new Map(currentSessions.map(session=>[session.sessionId,session]));
    const previousSessionsById=new Map(currentSessionsById);
    let mergedTotals=currentTotals;

    sessions.forEach(session=>{
      const previous=currentSessionsById.get(session.sessionId);
      if(previous){
        mergedTotals=subtractTotals(mergedTotals,getSessionTotalsDelta(previous));
      }
      mergedTotals=addTotals(mergedTotals,getSessionTotalsDelta(session));
      currentSessionsById.set(session.sessionId,session);
    });
    if(totals){
      mergedTotals=addTotals(
        mergedTotals,
        subtractTotals(totals,sumSessionTotals(sessions))
      );
    }

    const store=tx.objectStore(STORE_NAME);
    const mergedTrend=buildMergedTrendBuckets(currentBuckets,sessions,previousSessionsById,importedTrendBuckets);
    sessions.forEach(session=>store.put(session));
    if(latestTrace){
      tx.objectStore(TRACE_STORE_NAME).put(latestTrace);
    }
    tx.objectStore(TOTALS_STORE_NAME).put(mergedTotals);
    const trendStore=tx.objectStore(TREND_STORE_NAME);
    mergedTrend.deletedIds.forEach(id=>trendStore.delete(id));
    mergedTrend.buckets.forEach(bucket=>trendStore.put(bucket));
    trendStore.put({id:TREND_META_ID,schemaVersion:TREND_SCHEMA_VERSION});
    await txDone(tx);
    const importedSessionIds=new Set(sessions.map(session=>session.sessionId));
    fallbackSessions.length=0;
    fallbackSessions.push(...sessions, ...currentSessions.filter(session=>!importedSessionIds.has(session.sessionId)));
    fallbackLatestTrace=latestTrace || fallbackLatestTrace;
    fallbackTotals=normalizeTotalsRecord(mergedTotals);
    fallbackTrendBuckets.length=0;
    fallbackTrendBuckets.push(...mergedTrend.buckets);
    trendBucketsInitialized=true;
    persistBackupSnapshot();
    rememberImportedBackup(importKey);
    return sessions.length;
  }

  function importData(payload){
    return enqueueHistoryWrite(()=>importDataInternal(payload));
  }

  function waitForWrites(){
    return historyWriteChain;
  }

  async function exportData(){
    await ensureTrendBuckets();
    if(!supportsIndexedDB || hasBackupSnapshot){
      return {
        schemaVersion:2,
        exportedAt:new Date().toISOString(),
        sessions:getSortedFallbackSessions(),
        trendBuckets:fallbackTrendBuckets.map(normalizeTrendBucket).filter(Boolean),
        latestSessionTrace:fallbackLatestTrace ? normalizeLatestTraceRecord(fallbackLatestTrace) : null,
        historyTotals:normalizeTotalsRecord(fallbackTotals)
      };
    }
    const db=await openDb();
    const tx=db.transaction([STORE_NAME,TRACE_STORE_NAME,TOTALS_STORE_NAME,TREND_STORE_NAME],"readonly");
    const [rawSessions,rawTrace,rawTotals,rawTrendBuckets]=await Promise.all([
      requestToPromise(tx.objectStore(STORE_NAME).getAll(),"Failed to export sessions"),
      requestToPromise(tx.objectStore(TRACE_STORE_NAME).get("latest"),"Failed to export latest trace"),
      requestToPromise(tx.objectStore(TOTALS_STORE_NAME).get("totals"),"Failed to export history totals"),
      requestToPromise(tx.objectStore(TREND_STORE_NAME).getAll(),"Failed to export trend data")
    ]);
    await txDone(tx);
    return {
      schemaVersion:2,
      exportedAt:new Date().toISOString(),
      sessions:(rawSessions||[]).map(normalizeHistoryRecord).sort((a,b)=>Number(b.endedAt||0)-Number(a.endedAt||0)),
      trendBuckets:(rawTrendBuckets||[]).map(normalizeTrendBucket).filter(Boolean),
      latestSessionTrace:rawTrace ? normalizeLatestTraceRecord(rawTrace) : null,
      historyTotals:normalizeTotalsRecord(rawTotals)
    };
  }

  async function getStats(){
    const historyTotals=await readStoredTotals();

    return {
      completedSessions:historyTotals.completedSessions,
      totalCorrectAnswers:historyTotals.totalCorrectAnswers,
      totalDurationMs:historyTotals.totalDurationMs
    };
  }

  return {
    saveSession,
    saveLatestTrace,
    getAllSessions,
    getLatestTrace,
    getMostRecentHistorySettings,
    getSessionPage,
    getTrendData,
    clearAll,
    clearSessionsOnly,
    importData,
    exportData,
    waitForWrites,
    getStats
  };
})();

function buildSessionRecord(responseTimeStats){
  const totalItems=scoredItemCount;
  const totalQuestionsAsked=Math.max(0,totalItems);
  const thresholds=getThresholds();

  return normalizeHistoryRecord({
    sessionId:currentSessionId || generateSessionId(),
    startedAt:sessionStartedAt,
    endedAt:sessionEndedAt,
    status:sessionOutcome,
    arithmeticMode,
    nBackLevel,
    endCondition,
    durationMs:Math.max(0,sessionEndedAt-sessionStartedAt),
    accuracy:totalItems?correctAnswers/totalItems*100:0,
    correctAnswers,
    totalQuestionsAsked,
    averageResponseTimeMs:totalItems?totalResponseTime/totalItems:0,
    ...responseTimeStats,
    correctThreshold:thresholds.correct,
    incorrectThreshold:thresholds.incorrect,
    startingInterval,
    maximumInterval,
    minimumInterval,
    intervalIncrement,
    voice:selectedVoice,
    playbackSpeed,
    includeInTrends:sessionOutcome!=="Manually exited"
  });
}

function buildLatestTraceRecord(){
  const firstTraceIndex=nBackLevel;
  const lastTraceIndex=Math.max(
    firstTraceIndex,
    sessionIntervalTrace.length-(excludeLastQuestionFromTrace ? 1 : 0)
  );
  const trimmedTrace=new Array(Math.max(0,lastTraceIndex-firstTraceIndex));
  for(let sourceIndex=firstTraceIndex; sourceIndex<lastTraceIndex; sourceIndex++){
    const point=sessionIntervalTrace[sourceIndex];
    trimmedTrace[sourceIndex-firstTraceIndex]={
      questionNumber:sourceIndex-firstTraceIndex+1,
      interval:point.interval,
      timestamp:point.timestamp,
      responseTime:point.responseTime
    };
  }
  const totalQuestionsAsked=trimmedTrace.length;
  return normalizeLatestTraceRecord({
    sessionId:currentSessionId || generateSessionId(),
    startedAt:sessionStartedAt,
    endedAt:sessionEndedAt,
    status:sessionOutcome,
    nBackLevel,
    totalQuestionsAsked,
    trace:trimmedTrace
  });
}

function shouldStoreSession(record){
  const durationMs=Number(record?.durationMs)||0;
  const correctAnswersCount=Number(record?.correctAnswers)||0;
  return durationMs>=30000 && correctAnswersCount>=5;
}

const sessionDateTimeFormatter=new Intl.DateTimeFormat(undefined,{
  dateStyle:"medium",
  timeStyle:"short"
});
const shortChartDateFormatter=new Intl.DateTimeFormat(undefined,{
  month:"short",
  day:"numeric"
});
const chartDateWithYearFormatter=new Intl.DateTimeFormat(undefined,{
  month:"short",
  day:"numeric",
  year:"numeric"
});

function formatSessionDateTime(timestamp){
  return sessionDateTimeFormatter.format(new Date(timestamp));
}

function escapeSvgText(value){
  return String(value)
    .replace(/&/g,"&amp;")
    .replace(/</g,"&lt;")
    .replace(/>/g,"&gt;")
    .replace(/"/g,"&quot;")
    .replace(/'/g,"&#39;");
}

function getLabelIndices(count,maxLabels){
  if(count<=0) return [];
  if(count<=8) return Array.from({ length: count }, (_,index)=>index);

  const safeMaxLabels=Math.max(2,Number(maxLabels)||2);
  const step=Math.max(1,Math.ceil((count-1)/(safeMaxLabels-1)));
  const indices=[0];

  for(let index=step; index<count-1; index+=step){
    indices.push(index);
  }

  indices.push(count-1);
  return [...new Set(indices)].sort((a,b)=>a-b);
}

function getQuestionLabelIndices(count){
  if(count<=0) return [];
  if(count===1) return [0];

  const desiredLabels=count<=50 ? 7 : count<=200 ? 8 : count<=1000 ? 9 : 10;
  const rawStep=Math.max(1,Math.ceil(count/desiredLabels));
  const niceSteps=[1,2,5,10,20,50,100,200,500,1000];
  const step=niceSteps.find(value=>value>=rawStep) || niceSteps[niceSteps.length-1];
  const indices=[0];

  for(let questionNumber=step; questionNumber<count; questionNumber+=step){
    indices.push(questionNumber-1);
  }

  indices.push(count-1);
  return [...new Set(indices)].sort((a,b)=>a-b);
}

function formatChartDateLabel(timestamp,includeYear=false){
  const formatter=includeYear ? chartDateWithYearFormatter : shortChartDateFormatter;
  return formatter.format(new Date(timestamp));
}

function getLocalCalendarDayKey(timestamp){
  const date=new Date(Number(timestamp)||0);
  return [
    date.getFullYear(),
    String(date.getMonth()+1).padStart(2,"0"),
    String(date.getDate()).padStart(2,"0")
  ].join("-");
}

function getNextLocalCalendarDayStart(timestamp){
  const date=new Date(Number(timestamp)||0);
  date.setDate(date.getDate()+1);
  return new Date(date.getFullYear(),date.getMonth(),date.getDate()).getTime();
}

function addDailyTrendValue(buckets,dayKey,dayStart,value,weight){
  const numericValue=Number(value);
  const numericWeight=Number(weight);
  if(!Number.isFinite(numericValue) || !Number.isFinite(numericWeight) || numericWeight<=0) return;

  const bucket=buckets.get(dayKey) || {
    dayKey,
    dayStart,
    total:0,
    weightTotal:0,
    count:0
  };

  bucket.total += numericValue * numericWeight;
  bucket.weightTotal += numericWeight;
  bucket.count += 1;
  bucket.dayStart=Math.min(bucket.dayStart,dayStart);
  buckets.set(dayKey,bucket);
}

function addDailyTrendValues(accuracyBuckets,responseBuckets,session,weight){
  const numericWeight=Number(weight);
  const accuracy=Number(session?.accuracy);
  const responseTime=Number(session?.averageResponseTimeMs);
  if(!Number.isFinite(numericWeight) || numericWeight<=0) return;
  if(!Number.isFinite(accuracy) && !Number.isFinite(responseTime)) return;

  const timestamp=Number(session?.endedAt || session?.startedAt || Date.now());
  const date=new Date(timestamp);
  const year=date.getFullYear();
  const month=date.getMonth();
  const day=date.getDate();
  const dayKey=[
    year,
    String(month+1).padStart(2,"0"),
    String(day).padStart(2,"0")
  ].join("-");
  const dayStart=new Date(year,month,day).getTime();

  addDailyTrendValue(accuracyBuckets,dayKey,dayStart,accuracy,numericWeight);
  addDailyTrendValue(responseBuckets,dayKey,dayStart,responseTime,numericWeight);
}

function finalizeDailyTrendBuckets(buckets){
  const sortedBuckets=[...buckets.values()]
    .sort((a,b)=>a.dayStart-b.dayStart)
  if(!sortedBuckets.length) return [];

  const bucketByDayKey=new Map(sortedBuckets.map(bucket=>[bucket.dayKey,bucket]));
  const points=[];
  let cursorDayStart=sortedBuckets[0].dayStart;
  const lastDayStart=sortedBuckets[sortedBuckets.length-1].dayStart;

  while(cursorDayStart<=lastDayStart){
    const dayKey=getLocalCalendarDayKey(cursorDayStart);
    const bucket=bucketByDayKey.get(dayKey);
    if(bucket){
      points.push({
        dayKey:bucket.dayKey,
        dayStart:bucket.dayStart,
        value:bucket.weightTotal ? bucket.total / bucket.weightTotal : 0,
        count:bucket.count,
        weightTotal:bucket.weightTotal,
        label:formatChartDateLabel(bucket.dayStart,false)
      });
    }else{
      points.push({
        dayKey,
        dayStart:cursorDayStart,
        value:null,
        count:0,
        weightTotal:0,
        label:formatChartDateLabel(cursorDayStart,false),
        isGap:true
      });
    }
    cursorDayStart=getNextLocalCalendarDayStart(cursorDayStart);
  }

  return points;
}

function isTrendEligibleSession(session){
  return session?.includeInTrends!==false;
}

function isSessionInMode(session,mode){
  return (session?.arithmeticMode || defaultSettings.mode)===mode;
}

function isSessionInTrendGroup(session,mode,nBackLevel){
  return isTrendEligibleSession(session)
    && isSessionInMode(session,mode)
    && normalizeNBackLevel(session?.nBackLevel)===normalizeNBackLevel(nBackLevel);
}

function buildTrendDataForSessions(sessions,mode,nBackLevel){
  const resolvedNBackLevel=normalizeNBackLevel(nBackLevel);
  const accuracyBuckets=new Map();
  const responseBuckets=new Map();

  sessions.forEach(session=>{
    if(!isSessionInTrendGroup(session,mode,resolvedNBackLevel)) return;
    addDailyTrendValues(
      accuracyBuckets,
      responseBuckets,
      session,
      Number(session.totalQuestionsAsked)
    );
  });

  return {
    accuracyPoints:finalizeDailyTrendBuckets(accuracyBuckets),
    responsePoints:finalizeDailyTrendBuckets(responseBuckets),
    mode,
    nBackLevel:resolvedNBackLevel
  };
}

function getDailyTrendLabelCount(pointCount){
  if(pointCount<=7) return pointCount;
  if(pointCount<=14) return 6;
  if(pointCount<=30) return 7;
  if(pointCount<=90) return 8;
  return 9;
}

function formatChartValue(value,unit=""){
  const rounded=Math.round(Number(value)||0);
  return rounded.toLocaleString() + unit;
}

function formatChartExactValue(value,unit=""){
  const num=Number(value);
  if(!Number.isFinite(num)) return "0" + unit;
  const digits=Number.isInteger(num) ? 0 : 2;
  return num.toLocaleString(undefined,{
    minimumFractionDigits:0,
    maximumFractionDigits:digits
  }) + unit;
}

const chartInteractionState=new Map();
const latestIntervalOverviewCache=new WeakMap();
const latestIntervalChartViewState={
  mode:"overview",
  blockIndex:null,
  sessionKey:null
};
let latestHistoryChartContext={
  stats:null,
  latestTrace:null
};

function getChartThemeColors(){
  const styles=getComputedStyle(document.documentElement);
  return {
    accent:styles.getPropertyValue("--accent").trim() || "#2563eb",
    surface:styles.getPropertyValue("--surface").trim() || "#ffffff",
    text:styles.getPropertyValue("--text").trim() || "#17202a",
    muted:styles.getPropertyValue("--muted").trim() || "#5f6b7a",
    border:styles.getPropertyValue("--border").trim() || "#d7dde5"
  };
}

function getChartState(container){
  const key=container.id || container;
  if(!chartInteractionState.has(key)){
    chartInteractionState.set(key,{
      selectedIndex:null,
      hoverIndex:null,
      selectedAnchor:null,
      hoverAnchor:null,
      detailsEl:null,
      points:[],
      chartKey:key,
      boundHandlers:null,
      circles:[],
      circlesByPoint:new Map(),
      hitGroups:[],
      svg:null,
      chartWidth:720,
      chartHeight:260,
      colors:null,
      container:null,
      config:null,
      pendingPointer:null,
      pointerFrameId:null
    });
  }
  return chartInteractionState.get(key);
}

function ensureChartTooltip(container,detailsEl){
  if(!detailsEl) return null;
  if(detailsEl.parentElement!==container){
    container.appendChild(detailsEl);
  }
  detailsEl.classList.add("chart-tooltip");
  return detailsEl;
}

function ensureChartSurface(container){
  let surface=[...container.children].find(child=>child.classList && child.classList.contains("chart-surface")) || null;
  if(!surface){
    surface=document.createElement("div");
    surface.className="chart-surface";
    const detailsEl=container.querySelector(".chart-tooltip");
    if(detailsEl && detailsEl.parentElement===container){
      container.insertBefore(surface,detailsEl);
    }else{
      container.appendChild(surface);
    }
  }
  return surface;
}

function getChartTooltipPosition(point){
  const x=Number(point?.xPercent);
  const y=Number(point?.yPercent);
  const safeX=Number.isFinite(x) ? Math.max(0,Math.min(100,x)) : 50;
  const safeY=Number.isFinite(y) ? Math.max(0,Math.min(100,y)) : 50;
  const placementY=safeY > 60 ? "top" : "bottom";
  let placementX="center";
  if(safeX < 22){
    placementX="left";
  }else if(safeX > 78){
    placementX="right";
  }
  let transform="translate(-50%, calc(-100% - 10px))";
  if(placementX==="left" && placementY==="top"){
    transform="translate(0, calc(-100% - 10px))";
  }else if(placementX==="right" && placementY==="top"){
    transform="translate(-100%, calc(-100% - 10px))";
  }else if(placementX==="left" && placementY==="bottom"){
    transform="translate(0, 10px)";
  }else if(placementX==="right" && placementY==="bottom"){
    transform="translate(-100%, 10px)";
  }else if(placementY==="bottom"){
    transform="translate(-50%, 10px)";
  }
  return {
    left: `${safeX}%`,
    top: `${safeY}%`,
    transform
  };
}

function buildChartPointDetail(point,config,index){
  if(!point) return config.emptyDetailMessage || "Hover, tap, or click a point to inspect it.";

  const xLabelName=config.xDetailLabel || "X";
  const yLabelName=config.yDetailLabel || "Y";
  const summary=point.summary || `${xLabelName} ${index + 1}`;

  if(Array.isArray(point.seriesValues) && point.seriesValues.length){
    if(config.showExactPointDetails){
      const rows=point.seriesValues
        .filter(series=>series && (series.exactLabel || series.displayLabel))
        .map(series=>{
          const color=escapeSvgText(series.color || "var(--accent)");
          return `
            <div class="chart-tooltip-row">
              <span><span class="chart-tooltip-swatch" style="background:${color}"></span>${escapeSvgText(series.label || "Value")}</span>
              <strong>${escapeSvgText(series.exactLabel || series.displayLabel || "")}</strong>
            </div>
          `;
        })
        .join("");
      return `
        <div class="chart-tooltip-title">${escapeSvgText(summary)}</div>
        <div class="chart-tooltip-row"><span>${escapeSvgText(xLabelName)}</span><strong>${escapeSvgText(point.xExactLabel || point.xDisplayLabel || "")}</strong></div>
        ${rows}
      `;
    }

    const rows=point.seriesValues
      .filter(series=>series && (series.exactLabel || series.displayLabel))
      .map(series=>{
        const color=escapeSvgText(series.color || "var(--accent)");
        return `
          <div class="chart-tooltip-row">
            <span><span class="chart-tooltip-swatch" style="background:${color}"></span>${escapeSvgText(series.label || "Value")}</span>
            <strong>${escapeSvgText(series.exactLabel || series.displayLabel || "")}</strong>
          </div>
        `;
      })
      .join("");
    return `
      <div class="chart-tooltip-title">${escapeSvgText(summary)}</div>
      ${rows}
    `;
  }

  return `
    <div class="chart-tooltip-title">${escapeSvgText(summary)}</div>
    <div class="chart-tooltip-row"><span>${escapeSvgText(xLabelName)}</span><strong>${escapeSvgText(point.xExactLabel || point.xDisplayLabel || "")}</strong></div>
    <div class="chart-tooltip-row"><span>${escapeSvgText(yLabelName)}</span><strong>${escapeSvgText(point.yExactLabel || point.yDisplayLabel || "")}</strong></div>
  `;
}

function cacheChartRenderState(container,config,width,height){
  const state=getChartState(container);
  const circles=[...container.querySelectorAll("circle.chart-point")];
  const detailsEl=container.id ? document.getElementById(container.id.replace(/Chart$/,"Details")) : null;
  state.detailsEl=ensureChartTooltip(container,detailsEl);
  state.points=config.pointMeta || [];
  state.circles=circles;
  state.circlesByPoint=new Map();
  state.svg=container.querySelector("svg.chart-svg");
  state.chartWidth=width;
  state.chartHeight=height;
  state.colors=getChartThemeColors();
  state.container=container;
  state.config=config;

  const hitGroupsByIndex=new Map();
  circles.forEach(circle=>{
    const pointIndex=Number(circle.dataset.pointIndex);
    const x=Number(circle.getAttribute("cx"));
    const y=Number(circle.getAttribute("cy"));
    if(!Number.isFinite(pointIndex) || !Number.isFinite(x) || !Number.isFinite(y)) return;

    const pointCircles=state.circlesByPoint.get(pointIndex) || [];
    pointCircles.push(circle);
    state.circlesByPoint.set(pointIndex,pointCircles);

    const group=hitGroupsByIndex.get(pointIndex) || { index:pointIndex, x, entries:[] };
    group.entries.push({ circle, x, y });
    hitGroupsByIndex.set(pointIndex,group);
  });
  state.hitGroups=[...hitGroupsByIndex.values()].sort((a,b)=>a.x-b.x);

  if(state.selectedIndex!==null && state.selectedIndex>=state.points.length){
    state.selectedIndex=null;
  }

  if(state.hoverIndex!==null && state.hoverIndex>=state.points.length){
    state.hoverIndex=null;
  }
}

function applyChartState(container,config,changedIndices=null){
  const state=getChartState(container);
  const colors=state.colors || getChartThemeColors();
  const multiSeries=Array.isArray(config.series) && config.series.length>1;
  const baseRadius=Number.isFinite(Number(config.pointRadius)) ? Math.max(0,Number(config.pointRadius)) : 4.5;
  const hoverRadius=Number.isFinite(Number(config.pointHoverRadius)) ? Math.max(baseRadius,Number(config.pointHoverRadius)) : baseRadius + 1.2;
  const selectedRadius=Number.isFinite(Number(config.pointSelectedRadius)) ? Math.max(hoverRadius,Number(config.pointSelectedRadius)) : baseRadius + 2.2;
  const pointIndices=changedIndices
    ? [...new Set(changedIndices.filter(index=>index!==null && index!==undefined))]
    : [...state.circlesByPoint.keys()];

  pointIndices.forEach(pointIndex=>{
    const pointCircles=state.circlesByPoint.get(pointIndex) || [];
    const isSelected=pointIndex===state.selectedIndex;
    const isHovered=!isSelected && pointIndex===state.hoverIndex;
    const active=isSelected || isHovered;
    const radius=isSelected ? selectedRadius : isHovered ? hoverRadius : baseRadius;

    pointCircles.forEach(circle=>{
      const seriesIndex=Number(circle.dataset.seriesIndex);
      const seriesColor=multiSeries && config.series && config.series[seriesIndex]
        ? (config.series[seriesIndex].lineColor || config.series[seriesIndex].pointStroke || colors.accent)
        : colors.accent;

      circle.setAttribute("r",String(radius));
      if(multiSeries){
        circle.setAttribute("fill",active ? seriesColor : colors.surface);
        circle.setAttribute("stroke",active ? colors.surface : seriesColor);
      }else{
        circle.setAttribute("fill",active ? colors.accent : colors.surface);
        circle.setAttribute("stroke",active ? colors.surface : colors.accent);
      }
      circle.setAttribute("stroke-width",isSelected ? "3" : isHovered ? "2.5" : "2");
      circle.setAttribute("opacity",active ? "1" : "0.95");
      circle.style.cursor="pointer";
      circle.classList.toggle("is-selected",isSelected);
      circle.classList.toggle("is-hovered",isHovered);
    });
  });

  if(state.detailsEl){
    const activeIndex=state.hoverIndex!==null ? state.hoverIndex : state.selectedIndex;
    const activePoint=activeIndex!==null ? state.points[activeIndex] : null;
    const tooltipEl=state.detailsEl;
    if(tooltipEl){
      tooltipEl.hidden=!activePoint;
      if(activePoint){
        const detailHtml=buildChartPointDetail(activePoint,config,activeIndex);
        if(tooltipEl.innerHTML!==detailHtml){
          tooltipEl.innerHTML=detailHtml;
        }
        const activeAnchor=state.hoverAnchor || state.selectedAnchor || activePoint;
        const position=getChartTooltipPosition(activeAnchor);
        tooltipEl.style.setProperty("--chart-tooltip-left",position.left);
        tooltipEl.style.setProperty("--chart-tooltip-top",position.top);
        tooltipEl.style.setProperty("--chart-tooltip-transform",position.transform);
      }
    }
  }
}

function bindChartInteractions(container,config){
  const state=getChartState(container);
  if(state.boundHandlers){
    container.removeEventListener("pointermove",state.boundHandlers.pointermove);
    container.removeEventListener("pointerdown",state.boundHandlers.pointerdown);
    container.removeEventListener("pointerleave",state.boundHandlers.pointerleave);
    container.removeEventListener("pointercancel",state.boundHandlers.pointerleave);
  }
  if(state.pointerFrameId!==null){
    cancelAnimationFrame(state.pointerFrameId);
    state.pointerFrameId=null;
  }
  state.pendingPointer=null;
  state.selectedIndex=null;
  state.hoverIndex=null;
  state.selectedAnchor=null;
  state.hoverAnchor=null;

  const getLiveCircleHit=event=>{
    const liveState=getChartState(container);
    const groups=liveState.hitGroups;
    const svg=liveState.svg;
    if(!groups.length || !svg || !svg.isConnected) return null;

    const rect=svg.getBoundingClientRect();
    if(!rect.width || !rect.height) return null;
    const scaleX=rect.width/liveState.chartWidth;
    const scaleY=rect.height/liveState.chartHeight;
    const svgX=(event.clientX-rect.left)/scaleX;
    const maxConfiguredRadius=Math.max(
      Number(config.pointRadius)||4.5,
      Number(config.pointHoverRadius)||0,
      Number(config.pointSelectedRadius)||0
    );
    const maxHitRadius=Math.max(14,maxConfiguredRadius*3);

    let low=0;
    let high=groups.length;
    while(low<high){
      const mid=(low+high)>>1;
      if(groups[mid].x<svgX) low=mid+1;
      else high=mid;
    }

    let nearest=null;
    let nearestDistance=Infinity;
    const inspectGroup=group=>{
      const groupDistance=Math.abs(group.x-svgX)*scaleX;
      if(groupDistance>maxHitRadius) return false;

      group.entries.forEach(entry=>{
        if(!entry.circle.isConnected) return;
        const centerX=rect.left + entry.x*scaleX;
        const centerY=rect.top + entry.y*scaleY;
        const distance=Math.hypot(centerX-event.clientX,centerY-event.clientY);
        if(distance<nearestDistance){
          nearestDistance=distance;
          nearest={ entry, distance, centerX, centerY };
        }
      });
      return true;
    };

    for(let index=low; index<groups.length && inspectGroup(groups[index]); index++){}
    for(let index=low-1; index>=0 && inspectGroup(groups[index]); index--){}

    const radius=nearest?.entry?.circle ? Number(nearest.entry.circle.getAttribute("r")) || 4.5 : 4.5;
    const hitRadius=Math.max(14,radius*3);
    if(!nearest || nearestDistance>hitRadius) return null;

    const index=Number(nearest.entry.circle.dataset.pointIndex);
    if(!Number.isFinite(index)) return null;
    return {
      index,
      centerX:nearest.centerX,
      centerY:nearest.centerY
    };
  };

  const getAnchorFromHit=hit=>{
    if(!hit) return null;
    const rect=container.getBoundingClientRect();
    if(!rect.width || !rect.height) return null;
    return {
      xPercent:((hit.centerX-rect.left)/rect.width)*100,
      yPercent:((hit.centerY-rect.top)/rect.height)*100
    };
  };

  const processPointerMove=event=>{
    const hit=getLiveCircleHit(event);
    if(!hit){
      if(getChartState(container).hoverIndex!==null){
        clearChartHover(container,config);
      }
      return;
    }

    const currentState=getChartState(container);
    if(currentState.hoverIndex===hit.index){
      return;
    }
    setChartHover(container,hit.index,config,getAnchorFromHit(hit));
  };

  const handlePointerMove=event=>{
    state.pendingPointer={
      clientX:event.clientX,
      clientY:event.clientY
    };
    if(state.pointerFrameId!==null) return;
    state.pointerFrameId=requestAnimationFrame(()=>{
      state.pointerFrameId=null;
      const pendingPointer=state.pendingPointer;
      state.pendingPointer=null;
      if(pendingPointer){
        processPointerMove(pendingPointer);
      }
    });
  };

  const handlePointerDown=event=>{
    if(state.pointerFrameId!==null){
      cancelAnimationFrame(state.pointerFrameId);
      state.pointerFrameId=null;
      state.pendingPointer=null;
    }
    const hit=getLiveCircleHit(event);
    if(!hit){
      clearChartSelection(container,config);
      return;
    }

    event.preventDefault();
    event.stopPropagation();
    const anchor=getAnchorFromHit(hit);
    setChartSelection(container,hit.index,config,anchor);
    if(typeof config.onPointSelect==="function"){
      config.onPointSelect(hit.index,anchor,event);
    }
  };

  const handlePointerLeave=()=>{
    if(state.pointerFrameId!==null){
      cancelAnimationFrame(state.pointerFrameId);
      state.pointerFrameId=null;
    }
    state.pendingPointer=null;
    const currentState=getChartState(container);
    if(currentState.selectedIndex===null){
      clearChartHover(container,config);
      return;
    }
    const previousHoverIndex=currentState.hoverIndex;
    currentState.hoverIndex=null;
    currentState.hoverAnchor=null;
    applyChartState(container,config,[previousHoverIndex,currentState.selectedIndex]);
  };

  state.boundHandlers={
    pointermove:handlePointerMove,
    pointerdown:handlePointerDown,
    pointerleave:handlePointerLeave
  };

  container.addEventListener("pointermove",handlePointerMove);
  container.addEventListener("pointerdown",handlePointerDown);
  container.addEventListener("pointerleave",handlePointerLeave);
  container.addEventListener("pointercancel",handlePointerLeave);
}

function clearChartInteractions(container){
  const state=getChartState(container);
  if(state.boundHandlers){
    container.removeEventListener("pointermove",state.boundHandlers.pointermove);
    container.removeEventListener("pointerdown",state.boundHandlers.pointerdown);
    container.removeEventListener("pointerleave",state.boundHandlers.pointerleave);
    container.removeEventListener("pointercancel",state.boundHandlers.pointerleave);
    state.boundHandlers=null;
  }
  if(state.pointerFrameId!==null){
    cancelAnimationFrame(state.pointerFrameId);
    state.pointerFrameId=null;
  }
  state.pendingPointer=null;
  state.selectedIndex=null;
  state.hoverIndex=null;
  state.selectedAnchor=null;
  state.hoverAnchor=null;
  state.points=[];
  state.circles=[];
  state.circlesByPoint=new Map();
  state.hitGroups=[];
  state.svg=null;
  state.colors=null;
  state.container=null;
  state.config=null;
}

function setChartHover(container,index,config,anchor=null){
  const state=getChartState(container);
  const previousHoverIndex=state.hoverIndex;
  state.hoverIndex=index;
  state.hoverAnchor=anchor;
  applyChartState(container,config,[previousHoverIndex,index,state.selectedIndex]);
}

function setChartSelection(container,index,config,anchor=null){
  const state=getChartState(container);
  const previousSelectedIndex=state.selectedIndex;
  const previousHoverIndex=state.hoverIndex;
  state.selectedIndex=index;
  state.hoverIndex=index;
  state.selectedAnchor=anchor;
  state.hoverAnchor=anchor;
  applyChartState(container,config,[previousSelectedIndex,previousHoverIndex,index]);
}

function clearChartHover(container,config){
  const state=getChartState(container);
  const previousHoverIndex=state.hoverIndex;
  state.hoverIndex=null;
  state.hoverAnchor=null;
  applyChartState(container,config,[previousHoverIndex,state.selectedIndex]);
}

function clearChartSelection(container,config){
  const state=getChartState(container);
  const previousSelectedIndex=state.selectedIndex;
  const previousHoverIndex=state.hoverIndex;
  state.selectedIndex=null;
  state.hoverIndex=null;
  state.selectedAnchor=null;
  state.hoverAnchor=null;
  applyChartState(container,config,[previousSelectedIndex,previousHoverIndex]);
}

function buildChartPath(points){
  let path="";
  let started=false;
  points.forEach(point=>{
    if(!point){
      started=false;
      return;
    }
    path += `${started ? "L" : "M"} ${point.x.toFixed(2)} ${point.y.toFixed(2)} `;
    started=true;
  });
  return path.trim();
}

function getNiceTickStep(rawStep){
  const safeStep=Math.max(1,Number(rawStep)||1);
  const magnitude=Math.pow(10,Math.floor(Math.log10(safeStep)));
  const normalized=safeStep/magnitude;
  const niceMultipliers=[1,2,2.5,5,10];
  const multiplier=niceMultipliers.find(value=>value>=normalized) || 10;
  return multiplier*magnitude;
}

function getNiceMsTicks(min,max,desiredTickCount=5){
  return getHumanFriendlyMsTicks(min,max,desiredTickCount);
}

function getHumanFriendlyMsTicks(min,max,desiredTickCount=5,chartHeight=260){
  const safeMin=Number.isFinite(min) ? min : 0;
  const safeMax=Number.isFinite(max) ? max : safeMin + 1;
  const range=Math.max(1,safeMax-safeMin);
  const pad=Math.max(range*0.08,5);
  const paddedRange=Math.max(1,(safeMax + pad) - (safeMin - pad));
  const innerHeight=Math.max(120,Number(chartHeight)||260);
  const maxTickCount=11;
  const minTickCount=5;
  const rawStep=paddedRange/Math.max(1,desiredTickCount-1);
  const rawMagnitude=Math.pow(10,Math.floor(Math.log10(Math.max(1,rawStep))));
  const candidateMagnitudes=[1,2,2.5,5,10];
  const candidateSteps=[];

  for(let exponent=Math.floor(Math.log10(Math.max(1,rawStep)))-1; exponent<=Math.floor(Math.log10(Math.max(1,rawStep)))+2; exponent++){
    const magnitude=Math.pow(10,exponent);
    candidateMagnitudes.forEach(multiplier=>{
      const step=multiplier*magnitude;
      if(step>=5) candidateSteps.push(step);
    });
  }

  candidateSteps.push(rawMagnitude);
  const uniqueCandidateSteps=[...new Set(candidateSteps.filter(value=>Number.isFinite(value) && value>=5))].sort((a,b)=>a-b);
  let chosenStep=uniqueCandidateSteps[uniqueCandidateSteps.length-1] || Math.max(10,getNiceTickStep(rawStep));

  for(const step of uniqueCandidateSteps){
    const tickMin=Math.floor((safeMin-pad)/step)*step;
    const tickMax=Math.ceil((safeMax+pad)/step)*step;
    const tickCount=Math.round((tickMax-tickMin)/step)+1;
    if(tickCount>=minTickCount && tickCount<=maxTickCount){
      chosenStep=step;
      break;
    }
  }

  const tickStep=Math.max(5,chosenStep);
  const tickMin=Math.floor((safeMin-pad)/tickStep)*tickStep;
  const tickMax=Math.ceil((safeMax+pad)/tickStep)*tickStep;
  const ticks=[];

  for(let value=tickMin; value<=tickMax + tickStep/2; value+=tickStep){
    ticks.push(Math.round(value));
  }

  return { ticks, tickStep, tickMin, tickMax };
}

function getLatestIntervalTargetBlockCount(chartWidth=720){
  const usableWidth=Math.max(320,chartWidth-140);
  return Math.max(22,Math.min(60,Math.round(usableWidth/13)));
}

function getLatestIntervalBlockSize(pointCount,chartWidth=720){
  if(pointCount<=75) return 1;

  const targetBlocks=getLatestIntervalTargetBlockCount(chartWidth);
  const rawStep=Math.max(1,Math.ceil(pointCount/targetBlocks));
  const niceSteps=[2,3,4,5,6,8,10,12,15,20,25,30,40,50,75,100,125,150,200,250,300,400,500,750,1000,1500,2000,2500,5000];
  return niceSteps.find(value=>value>=rawStep) || niceSteps[niceSteps.length-1];
}

function getLatestIntervalSessionKey(latestTrace){
  return latestTrace?.sessionId || `${Number(latestTrace?.startedAt)||0}-${Number(latestTrace?.endedAt)||0}`;
}

function buildLatestIntervalOverviewBlocks(tracePoints,chartWidth=720){
  const pointCount=tracePoints.length;
  const blockSize=getLatestIntervalBlockSize(pointCount,chartWidth);
  const cachedByBlockSize=latestIntervalOverviewCache.get(tracePoints);
  const cachedOverview=cachedByBlockSize?.get(blockSize);
  if(cachedOverview && cachedOverview.pointCount===pointCount){
    return cachedOverview.result;
  }

  const blocks=[];

  for(let start=0; start<pointCount; start+=blockSize){
    const end=Math.min(pointCount,start+blockSize);
    let intervalTotal=0;
    let intervalCount=0;
    let responseTotal=0;
    let responseCount=0;

    for(let index=start; index<end; index++){
      const point=tracePoints[index];
      const intervalValue=Number(point?.interval);
      const responseValue=Number(point?.responseTime);
      if(Number.isFinite(intervalValue)){
        intervalTotal+=intervalValue;
        intervalCount++;
      }
      if(Number.isFinite(responseValue)){
        responseTotal+=responseValue;
        responseCount++;
      }
    }

    const intervalAverage=intervalCount
      ? intervalTotal/intervalCount
      : NaN;
    const responseAverage=responseCount
      ? responseTotal/responseCount
      : NaN;
    const startQuestion=Number(tracePoints[start]?.questionNumber)||start+1;
    const endQuestion=Number(tracePoints[end-1]?.questionNumber)||end;

    blocks.push({
      startIndex:start,
      endIndex:end-1,
      startQuestion,
      endQuestion,
      blockSize:end-start,
      interval:intervalAverage,
      responseTime:responseAverage,
      summary:startQuestion===endQuestion
        ? `Question ${startQuestion}`
        : `Questions ${startQuestion}-${endQuestion}`,
      rangeLabel:startQuestion===endQuestion
        ? `${startQuestion}`
        : `${startQuestion}-${endQuestion}`,
      intervalLabel:Number.isFinite(intervalAverage) ? formatChartExactValue(intervalAverage," ms") : "n/a",
      responseLabel:Number.isFinite(responseAverage) ? formatChartExactValue(responseAverage," ms") : "n/a"
    });
  }

  const result={ blockSize, blocks };
  const nextCache=cachedByBlockSize || new Map();
  nextCache.set(blockSize,{ pointCount, result });
  if(!cachedByBlockSize){
    latestIntervalOverviewCache.set(tracePoints,nextCache);
  }
  return result;
}

function buildLatestIntervalDetailPoints(tracePoints,block){
  if(!block) return [];
  return tracePoints.slice(block.startIndex,block.endIndex + 1).map((point,index)=>({
    questionNumber:Number(point.questionNumber)||block.startQuestion + index,
    interval:Number(point.interval),
    responseTime:Number(point.responseTime),
    timestamp:Number(point.timestamp)||0
  }));
}

function setLatestIntervalChartMode(mode,blockIndex=null){
  latestIntervalChartViewState.mode=mode;
  latestIntervalChartViewState.blockIndex=blockIndex;
}

function syncLatestIntervalChartSession(latestTrace){
  const traceSessionKey=getLatestIntervalSessionKey(latestTrace);
  if(latestIntervalChartViewState.sessionKey===traceSessionKey) return false;
  latestIntervalChartViewState.sessionKey=traceSessionKey;
  setLatestIntervalChartMode("overview",null);
  clearChartInteractions(latestIntervalChart);
  return true;
}

function renderLatestIntervalChartEmptyState(message){
  clearChartInteractions(latestIntervalChart);
  ensureChartSurface(latestIntervalChart).innerHTML=`<div class="chart-empty">${escapeSvgText(message)}</div>`;
  latestIntervalBackBtn.classList.add("hidden");
  if(latestIntervalCaption){
    latestIntervalCaption.textContent=message;
  }
  if(latestIntervalDetails){
    latestIntervalDetails.hidden=true;
    latestIntervalDetails.innerHTML="";
  }
}

function renderLatestIntervalChartOverview(latestTrace,overviewData){
  const overviewPointMeta=overviewData.blocks.map(block=>({
    xExactLabel:block.summary,
    summary:block.summary,
    seriesValues:[
      {
        label:"Interval avg",
        exactLabel:block.intervalLabel,
        color:"var(--accent)"
      },
      {
        label:"Response avg",
        exactLabel:block.responseLabel,
        color:"var(--good)"
      }
    ].filter(series=>series.exactLabel)
  }));

  const overviewIntervalValues=overviewData.blocks.map(block=>Number(block.interval));
  const overviewResponseValues=overviewData.blocks.map(block=>Number(block.responseTime));
  const overviewResponseValuesForScale=overviewResponseValues.filter(value=>Number.isFinite(value));
  const overviewMax=Math.max(...overviewIntervalValues, ...(overviewResponseValuesForScale.length ? overviewResponseValuesForScale : [0]));
  const overviewMin=Math.min(...overviewIntervalValues, ...(overviewResponseValuesForScale.length ? overviewResponseValuesForScale : [0]));

    renderOverlayLineChart(latestIntervalChart,{
    series:[
      {
        label:"Interval",
        values:overviewIntervalValues,
        lineColor:"var(--accent)",
        pointTitles:overviewPointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[0]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      },
      {
        label:"Response time",
        values:overviewResponseValues,
        lineColor:"var(--good)",
        lineOpacity:0.62,
        lineWidth:2,
        pointTitles:overviewPointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[1]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      }
      ],
      xLabels:overviewData.blocks.map(block=>block.rangeLabel),
      pointMeta:overviewPointMeta,
    xDetailLabel:"Question block",
    yDetailLabel:"Milliseconds",
    yMin:overviewMin,
    yMax:overviewMax,
    xAxisLabel:"Question blocks",
    ariaLabel:"Latest session interval and response time overview chart",
    emptyMessage:"No interval data is available yet.",
      yFormatter:value=>formatChartValue(value," ms"),
      maxXLabels:overviewData.blocks.length > 20 ? 6 : overviewData.blocks.length > 10 ? 5 : 6,
      floorAtZero:false,
      height:258,
      margin:{ top:18, right:14, bottom:48, left:52 },
      pointRadius:3.6,
      pointHoverRadius:4.8,
      pointSelectedRadius:6.0,
      labelFontSize:10,
      axisLabelFontSize:10,
      onPointSelect:index=>{
        clearChartInteractions(latestIntervalChart);
        setLatestIntervalChartMode("detail",index);
        renderLatestIntervalChart(latestTrace);
    }
  });

  latestIntervalBackBtn.classList.add("hidden");
  if(latestIntervalCaption){
    latestIntervalCaption.textContent=overviewData.blockSize===1
      ? "Overview shows individual questions. Tap a point to inspect it."
      : `Overview shows ${overviewData.blockSize}-question blocks. Tap a block to zoom into its questions.`;
  }
}

function renderLatestIntervalChartRaw(latestTrace){
  setLatestIntervalChartMode("overview",null);
  const tracePoints=Array.isArray(latestTrace?.trace) ? latestTrace.trace : [];
  const intervalValues=tracePoints.map(point=>Number(point.interval)).filter(Number.isFinite);
  const responseTimeValues=tracePoints.map(point=>Number(point.responseTime)).filter(Number.isFinite);
  const responseValuesForScale=responseTimeValues.filter(value=>Number.isFinite(value));
  const rawMax=Math.max(...intervalValues, ...(responseValuesForScale.length ? responseValuesForScale : [0]));
  const rawMin=Math.min(...intervalValues, ...(responseValuesForScale.length ? responseValuesForScale : [0]));
  const pointMeta=tracePoints.map((point,index)=>{
    const xExact=`Question ${Number(point.questionNumber)||index+1}`;
    const yExact=formatChartExactValue(Number(point.interval)||0," ms");
    const responseTimeValue=Number(point.responseTime);
    const responseTimeExact=Number.isFinite(responseTimeValue) ? formatChartExactValue(responseTimeValue," ms") : "";
    return {
      xExactLabel:xExact,
      summary:xExact,
      seriesValues:[
        {
          label:"Interval",
          exactLabel:yExact,
          color:"var(--accent)"
        },
        {
          label:"Response time",
          exactLabel:responseTimeExact,
          color:"var(--good)"
        }
      ].filter(series=>series.exactLabel)
    };
  });

    renderOverlayLineChart(latestIntervalChart,{
    series:[
      {
        label:"Interval",
        values:intervalValues,
        lineColor:"var(--accent)",
        pointTitles:pointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[0]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      },
      {
        label:"Response time",
        values:tracePoints.map(point=>Number(point.responseTime)),
        lineColor:"var(--good)",
        lineOpacity:0.62,
        lineWidth:2,
        pointTitles:pointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[1]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      }
    ],
    xLabels:tracePoints.map(point=>String(point.questionNumber)),
    pointMeta,
    xLabelMode:"questionNumber",
    xDetailLabel:"Question",
    yDetailLabel:"Milliseconds",
    showExactPointDetails:true,
    yMin:rawMin,
    yMax:rawMax,
    xAxisLabel:"Question number",
    ariaLabel:"Latest session interval and response time chart",
    emptyMessage:"No interval data is available yet.",
      yFormatter:value=>formatChartValue(value," ms"),
      maxXLabels:tracePoints.length > 30 ? 6 : tracePoints.length > 15 ? 5 : 6,
      floorAtZero:false,
      height:236,
      margin:{ top:16, right:14, bottom:42, left:74 },
      pointRadius:3.6,
      pointHoverRadius:4.8,
      pointSelectedRadius:6.0,
      labelFontSize:12,
      axisLabelFontSize:12
    });

  latestIntervalBackBtn.classList.add("hidden");
  if(latestIntervalCaption){
    latestIntervalCaption.textContent=tracePoints.length===1
      ? "Hover or tap the point to inspect exact values."
      : "Hover or tap a point to inspect exact values.";
  }
}

function renderLatestIntervalChartDetail(latestTrace,detailBlock){
  const tracePoints=Array.isArray(latestTrace?.trace) ? latestTrace.trace : [];
  const detailPoints=buildLatestIntervalDetailPoints(tracePoints,detailBlock);
  const intervalValues=detailPoints.map(point=>Number(point.interval)).filter(Number.isFinite);
  const responseTimeValues=detailPoints.map(point=>Number(point.responseTime)).filter(Number.isFinite);
  const maxInterval=Math.max(...intervalValues, ...(responseTimeValues.length ? responseTimeValues : [0]));
  const minValue=Math.min(...intervalValues, ...(responseTimeValues.length ? responseTimeValues : [0]));
  const detailRange=Math.max(1,maxInterval-minValue);
  const detailPad=Math.max(50,Math.ceil(detailRange*0.12));
  const detailMin=Math.max(0,minValue-detailPad);
  const detailMax=maxInterval+detailPad;
  const pointMeta=detailPoints.map((point,index)=>{
    const xExact=`Question ${Number(point.questionNumber)||index+1}`;
    const yExact=formatChartExactValue(Number(point.interval)||0," ms");
    const responseTimeValue=Number(point.responseTime);
    const responseTimeExact=Number.isFinite(responseTimeValue) ? formatChartExactValue(responseTimeValue," ms") : "";
    return {
      xExactLabel:xExact,
      summary:xExact,
      seriesValues:[
        {
          label:"Interval",
          exactLabel:yExact,
          color:"var(--accent)"
        },
        {
          label:"Response time",
          exactLabel:responseTimeExact,
          color:"var(--good)"
        }
      ].filter(series=>series.exactLabel)
    };
  });

    renderOverlayLineChart(latestIntervalChart,{
    series:[
      {
        label:"Interval",
        values:detailPoints.map(point=>Number(point.interval)),
        lineColor:"var(--accent)",
        pointTitles:pointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[0]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      },
      {
        label:"Response time",
        values:detailPoints.map(point=>Number(point.responseTime)),
        lineColor:"var(--good)",
        lineOpacity:0.62,
        lineWidth:2,
        pointTitles:pointMeta.map(point=>`${point.xExactLabel} - ${point.seriesValues[1]?.exactLabel || ""}`),
        yFormatter:value=>formatChartValue(value," ms")
      }
    ],
    xLabels:detailPoints.map(point=>String(point.questionNumber)),
    pointMeta,
    xLabelMode:"questionNumber",
    xDetailLabel:"Question",
    yDetailLabel:"Milliseconds",
    showExactPointDetails:true,
    yMin:detailMin,
    yMax:detailMax,
    xAxisLabel:"Question number",
    ariaLabel:"Latest session interval and response time chart",
    emptyMessage:"No interval data is available yet.",
      yFormatter:value=>formatChartValue(value," ms"),
      maxXLabels:detailPoints.length > 30 ? 6 : detailPoints.length > 15 ? 5 : 6,
      floorAtZero:false,
      height:252,
      margin:{ top:18, right:14, bottom:48, left:76 },
      pointRadius:3.6,
      pointHoverRadius:4.8,
      pointSelectedRadius:6.0,
      labelFontSize:11,
      axisLabelFontSize:11
    });

  latestIntervalBackBtn.classList.remove("hidden");
  if(latestIntervalCaption){
    const startQuestion=Number(detailBlock.startQuestion)||1;
    const endQuestion=Number(detailBlock.endQuestion)||startQuestion;
    latestIntervalCaption.textContent=`Showing questions ${startQuestion}-${endQuestion}. Tap Back to Overview to return.`;
  }
}

function renderLineChart(container,config){
  const detailsEl=container.id ? document.getElementById(container.id.replace(/Chart$/,"Details")) : null;
  const rawValues=Array.isArray(config.values) ? config.values.slice() : [];
  const xValuesRaw=Array.isArray(config.xValues) ? config.xValues.map(value=>Number(value)) : null;
  const slotCount=Math.max(rawValues.length, xValuesRaw ? xValuesRaw.length : 0);
  const numericValues=rawValues.map(value=>{
    if(value===null || value===undefined || value==="") return null;
    const numeric=Number(value);
    return Number.isFinite(numeric) ? numeric : null;
  });
  const finiteValues=numericValues.filter(value=>Number.isFinite(value));
  if(!slotCount || !finiteValues.length){
    clearChartInteractions(container);
    ensureChartSurface(container).innerHTML=`<div class="chart-empty">${escapeSvgText(config.emptyMessage || "No data available.")}</div>`;
    if(detailsEl){
      detailsEl.hidden=true;
      detailsEl.innerHTML="";
    }
    return;
  }

  const width=720;
  const height=260;
  const margin=config.margin || { top:18, right:18, bottom:50, left:60 };
  const innerWidth=width-margin.left-margin.right;
  const innerHeight=height-margin.top-margin.bottom;
  let min=Number.isFinite(config.yMin) ? config.yMin : Math.min(...finiteValues);
  let max=Number.isFinite(config.yMax) ? config.yMax : Math.max(...finiteValues);
  const xValues=xValuesRaw && xValuesRaw.length===slotCount && xValuesRaw.every(Number.isFinite) ? xValuesRaw : null;
  const hasXValues=Array.isArray(xValues) && xValues.length===slotCount;

  if(min===max){
    min-=1;
    max+=1;
  }else if(!Number.isFinite(config.yMin) || !Number.isFinite(config.yMax)){
    const padding=(max-min)*0.08;
    if(!Number.isFinite(config.yMin)) min-=padding;
    if(!Number.isFinite(config.yMax)) max+=padding;
  }

  if(config.floorAtZero && min>0){
    min=0;
  }
  if(config.floorAtZero && min<0){
    min=0;
  }
  if(max<=min){
    max=min+1;
  }

  const yTickStep=Number.isFinite(config.yTickStep) && config.yTickStep>0 ? config.yTickStep : null;
  const yTicksInfo=config.yTickMode==="niceMs" ? getHumanFriendlyMsTicks(min,max,config.desiredYTickCount || 5) : null;
  if(yTicksInfo){
    min=yTicksInfo.tickMin;
    max=yTicksInfo.tickMax;
  }
  if(yTickStep){
    min=Math.floor(min/yTickStep)*yTickStep;
    max=Math.ceil(max/yTickStep)*yTickStep;
  }

  const safeRange=max-min || 1;
  const pointCount=slotCount;
  const xMin=hasXValues ? Math.min(...xValues) : 0;
  const xMax=hasXValues ? Math.max(...xValues) : Math.max(1,pointCount-1);
  const xSafeRange=Math.max(1,xMax-xMin);
  const xPosition=index=>{
    if(pointCount===1) return margin.left + innerWidth/2;
    if(hasXValues){
      return margin.left + (((xValues[index]-xMin)/xSafeRange)*innerWidth);
    }
    return margin.left + (innerWidth*(index/(pointCount-1)));
  };
  const yPosition=value=>margin.top + innerHeight - (((value-min)/safeRange)*innerHeight);
  const points=numericValues.map((numeric,index)=>{
    if(!Number.isFinite(numeric)) return null;
    return {
      x:xPosition(index),
      y:yPosition(numeric)
    };
  });
  const path=points
    .filter(Boolean)
    .map((point,index)=>(index===0 ? "M" : "L") + " " + point.x.toFixed(2) + " " + point.y.toFixed(2))
    .join(" ");
  const xLabelIndices=config.xLabelMode==="questionNumber"
    ? getQuestionLabelIndices(pointCount)
    : getLabelIndices(pointCount,config.maxXLabels || 6);
  const tickCount=4;
  const yTickCount=Math.max(1,Math.round((max-min)/(yTickStep || (safeRange/tickCount)))) ;
  const yTicks=yTicksInfo ? yTicksInfo.ticks : yTickStep ? Array.from({ length: yTickCount + 1 }, (_,index)=>min + (index*yTickStep)) : Array.from({ length: tickCount + 1 }, (_,index)=>min + (safeRange*(index/tickCount)));

  const xAxisLabel=escapeSvgText(config.xAxisLabel || "");
  const yAxisLabel=escapeSvgText(config.yAxisLabel || "");
  const ariaLabel=escapeSvgText(config.ariaLabel || config.title || "Chart");
  const lineColor=config.lineColor || "var(--accent)";
  const pointFill=config.pointFill || "var(--surface)";
  const pointStroke=config.pointStroke || "var(--accent)";
  const gridColor=config.gridColor || "var(--border)";
  const textColor=config.textColor || "var(--muted)";
  const labelFontSize=Number.isFinite(Number(config.labelFontSize)) ? Math.max(8,Number(config.labelFontSize)) : 12;
  const axisLabelFontSize=Number.isFinite(Number(config.axisLabelFontSize)) ? Math.max(8,Number(config.axisLabelFontSize)) : labelFontSize;
  const pointRadius=Number.isFinite(Number(config.pointRadius)) ? Math.max(0,Number(config.pointRadius)) : null;
  const showPoints=config.showPoints !== false;
  const interactive=config.interactive !== false;

  let svg=`<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${ariaLabel}" class="chart-svg">`;
  svg+=`<rect x="0" y="0" width="${width}" height="${height}" fill="transparent"></rect>`;

  yTicks.forEach(tick=>{
    const y=yPosition(tick);
    svg+=`<line x1="${margin.left}" y1="${y.toFixed(2)}" x2="${width-margin.right}" y2="${y.toFixed(2)}" stroke="${gridColor}" stroke-width="1"></line>`;
    svg+=`<text x="${margin.left-8}" y="${(y+4).toFixed(2)}" text-anchor="end" fill="${textColor}" font-size="${labelFontSize}">${escapeSvgText(config.yFormatter ? config.yFormatter(tick) : formatChartValue(tick))}</text>`;
  });

  svg+=`<line x1="${margin.left}" y1="${margin.top}" x2="${margin.left}" y2="${height-margin.bottom}" stroke="${gridColor}" stroke-width="1"></line>`;
  svg+=`<line x1="${margin.left}" y1="${height-margin.bottom}" x2="${width-margin.right}" y2="${height-margin.bottom}" stroke="${gridColor}" stroke-width="1"></line>`;

  if(pointCount>1){
    svg+=`<path d="${path}" fill="none" stroke="${lineColor}" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"></path>`;
  }

  if(showPoints){
    points.forEach((point,index)=>{
      if(!point) return;
      const title=config.pointTitles && config.pointTitles[index] ? config.pointTitles[index] : "";
      const radius=pointRadius !== null ? pointRadius : (pointCount===1 ? 5 : 4.5);
      svg+=`<circle class="chart-point" data-point-index="${index}" cx="${point.x.toFixed(2)}" cy="${point.y.toFixed(2)}" r="${radius}" fill="${pointFill}" stroke="${pointStroke}" stroke-width="2" aria-label="${escapeSvgText(title || `Point ${index + 1}`)}"></circle>`;
    });
  }

  xLabelIndices.forEach(index=>{
    const x=xPosition(index);
    const label=config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1);
    const anchor=index===0 ? "start" : index===pointCount-1 ? "end" : "middle";
    svg+=`<text x="${x.toFixed(2)}" y="${height-14}" text-anchor="${anchor}" fill="${textColor}" font-size="${labelFontSize}">${escapeSvgText(label)}</text>`;
  });

  if(xAxisLabel){
    svg+=`<text x="${(margin.left + innerWidth/2).toFixed(2)}" y="${height-2}" text-anchor="middle" fill="${textColor}" font-size="${axisLabelFontSize}">${xAxisLabel}</text>`;
  }

  if(yAxisLabel){
    svg+=`<text x="14" y="${(margin.top + innerHeight/2).toFixed(2)}" text-anchor="middle" fill="${textColor}" font-size="${axisLabelFontSize}" transform="rotate(-90 14 ${(margin.top + innerHeight/2).toFixed(2)})">${yAxisLabel}</text>`;
  }

  svg+="</svg>";
  ensureChartSurface(container).innerHTML=svg;

  const pointMeta=Array.isArray(config.pointMeta) ? config.pointMeta : rawValues.map((value,index)=>({
    xExactLabel:config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1),
    yExactLabel:Number.isFinite(numericValues[index]) ? (config.yFormatter ? config.yFormatter(numericValues[index]) : formatChartValue(numericValues[index])) : "",
    summary:`Point ${index + 1}`
  }));
  const mergedPointMeta=pointMeta.map((point,index)=>({
    ...point,
    xPercent:xPosition(index) / width * 100,
    yPercent:points[index] ? (points[index].y / height) * 100 : 50
  }));

  const state=getChartState(container);
  state.chartKey=container.id || container;

  config.pointMeta=mergedPointMeta;
  if(interactive){
    cacheChartRenderState(container,config,width,height);
    state.points=mergedPointMeta;
    bindChartInteractions(container,config);
    applyChartState(container,config);
  }else{
    clearChartInteractions(container);
    if(detailsEl){
      detailsEl.hidden=true;
      detailsEl.innerHTML="";
    }
  }
}

function renderOverlayLineChart(container,config){
  const seriesConfigs=Array.isArray(config.series) ? config.series.filter(series=>series && Array.isArray(series.values)) : [];
  if(!seriesConfigs.length){
    renderLineChart(container,config);
    return;
  }

  const width=720;
  const height=config.height || 290;
  const margin=config.margin || { top:22, right:18, bottom:60, left:72 };
  const innerWidth=width-margin.left-margin.right;
  const innerHeight=height-margin.top-margin.bottom;
  const pointCount=Math.max(...seriesConfigs.map(series=>series.values.length),0);
  const allValues=seriesConfigs.flatMap(series=>series.values.map(value=>Number(value)).filter(Number.isFinite));
  let min=Number.isFinite(config.yMin) ? config.yMin : Math.min(...allValues);
  let max=Number.isFinite(config.yMax) ? config.yMax : Math.max(...allValues);

  if(!allValues.length){
    clearChartInteractions(container);
    ensureChartSurface(container).innerHTML=`<div class="chart-empty">${escapeSvgText(config.emptyMessage || "No data available.")}</div>`;
    return;
  }

  if(min===max){
    min-=1;
    max+=1;
  }else if(!Number.isFinite(config.yMin) || !Number.isFinite(config.yMax)){
    const padding=(max-min)*0.08;
    if(!Number.isFinite(config.yMin)) min-=padding;
    if(!Number.isFinite(config.yMax)) max+=padding;
  }

  if(config.floorAtZero && min>0){
    min=0;
  }

  const yTicksInfo=getHumanFriendlyMsTicks(min,max,5,innerHeight);
  const yTicks=yTicksInfo.ticks;
  min=yTicksInfo.tickMin;
  max=yTicksInfo.tickMax;

  const safeRange=max-min || 1;
  const xPosition=index=>{
    if(pointCount===1) return margin.left + innerWidth/2;
    return margin.left + (innerWidth*(index/Math.max(1,pointCount-1)));
  };
  const yPosition=value=>margin.top + innerHeight - (((value-min)/safeRange)*innerHeight);
  const xLabelIndices=config.xLabelMode==="questionNumber"
    ? getQuestionLabelIndices(pointCount)
    : getLabelIndices(pointCount,config.maxXLabels || 6);
  const xAxisLabel=escapeSvgText(config.xAxisLabel || "");
  const yAxisLabel=escapeSvgText(config.yAxisLabel || "");
  const ariaLabel=escapeSvgText(config.ariaLabel || config.title || "Chart");
  const gridColor=config.gridColor || "var(--border)";
  const textColor=config.textColor || "var(--muted)";
  const colors=getChartThemeColors();
  const labelFontSize=Number.isFinite(Number(config.labelFontSize)) ? Math.max(8,Number(config.labelFontSize)) : 12;
  const axisLabelFontSize=Number.isFinite(Number(config.axisLabelFontSize)) ? Math.max(8,Number(config.axisLabelFontSize)) : labelFontSize;
  const pointRadius=Number.isFinite(Number(config.pointRadius)) ? Math.max(0,Number(config.pointRadius)) : 4.5;
  const seriesPoints=seriesConfigs.map(series=>series.values.map((value,index)=>{
    const numeric=Number(value);
    if(!Number.isFinite(numeric)) return null;
    return {
      x:xPosition(index),
      y:yPosition(numeric),
      value:numeric
    };
  }));

  let svg=`<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${ariaLabel}" class="chart-svg">`;
  svg+=`<rect x="0" y="0" width="${width}" height="${height}" fill="transparent"></rect>`;

  yTicks.forEach(tick=>{
    const y=yPosition(tick);
    svg+=`<line x1="${margin.left}" y1="${y.toFixed(2)}" x2="${width-margin.right}" y2="${y.toFixed(2)}" stroke="${gridColor}" stroke-width="1"></line>`;
    svg+=`<text x="${margin.left-10}" y="${(y+4).toFixed(2)}" text-anchor="end" fill="${textColor}" font-size="${labelFontSize}">${escapeSvgText(config.yFormatter ? config.yFormatter(tick) : formatChartValue(tick))}</text>`;
  });

  svg+=`<line x1="${margin.left}" y1="${margin.top}" x2="${margin.left}" y2="${height-margin.bottom}" stroke="${gridColor}" stroke-width="1"></line>`;
  svg+=`<line x1="${margin.left}" y1="${height-margin.bottom}" x2="${width-margin.right}" y2="${height-margin.bottom}" stroke="${gridColor}" stroke-width="1"></line>`;

  seriesConfigs.forEach((series,seriesIndex)=>{
    const lineColor=series.lineColor || series.pointStroke || colors.accent;
    const lineOpacity=Number.isFinite(Number(series.lineOpacity)) ? Math.max(0,Math.min(1,Number(series.lineOpacity))) : 1;
    const lineWidth=Number.isFinite(Number(series.lineWidth)) ? Math.max(1,Number(series.lineWidth)) : 3;
    const path=buildChartPath(seriesPoints[seriesIndex]);
    if(path){
      svg+=`<path d="${path}" fill="none" stroke="${lineColor}" stroke-opacity="${lineOpacity}" stroke-width="${lineWidth}" stroke-linecap="round" stroke-linejoin="round"></path>`;
    }
  });

  seriesConfigs.forEach((series,seriesIndex)=>{
    const lineColor=series.lineColor || series.pointStroke || colors.accent;
    const seriesLabel=series.label || `Series ${seriesIndex + 1}`;
    seriesPoints[seriesIndex].forEach((point,index)=>{
      if(!point) return;
      const title=series.pointTitles && series.pointTitles[index] ? series.pointTitles[index] : `${seriesLabel} ${index + 1}`;
      svg+=`<circle class="chart-point" data-point-index="${index}" data-series-index="${seriesIndex}" cx="${point.x.toFixed(2)}" cy="${point.y.toFixed(2)}" r="${pointRadius}" fill="${colors.surface}" stroke="${lineColor}" stroke-width="2" aria-label="${escapeSvgText(title)}"></circle>`;
    });
  });

  xLabelIndices.forEach(index=>{
    const x=xPosition(index);
    const label=config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1);
    const anchor=index===0 ? "start" : index===pointCount-1 ? "end" : "middle";
    svg+=`<text x="${x.toFixed(2)}" y="${height-14}" text-anchor="${anchor}" fill="${textColor}" font-size="${labelFontSize}">${escapeSvgText(label)}</text>`;
  });

  if(xAxisLabel){
    svg+=`<text x="${(margin.left + innerWidth/2).toFixed(2)}" y="${height-2}" text-anchor="middle" fill="${textColor}" font-size="${axisLabelFontSize}">${xAxisLabel}</text>`;
  }

  if(yAxisLabel){
    svg+=`<text x="14" y="${(margin.top + innerHeight/2).toFixed(2)}" text-anchor="middle" fill="${textColor}" font-size="${axisLabelFontSize}" transform="rotate(-90 14 ${(margin.top + innerHeight/2).toFixed(2)})">${yAxisLabel}</text>`;
  }

  svg+="</svg>";
  ensureChartSurface(container).innerHTML=svg;

  const pointMetaBase=Array.isArray(config.pointMeta) ? config.pointMeta : Array.from({ length: pointCount }, (_,index)=>({
    xExactLabel:config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1),
    summary:config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1)
  }));
  const pointMeta=pointMetaBase.map((point,index)=>{
    const xExactLabel=point.xExactLabel || (config.xLabels && config.xLabels[index] ? config.xLabels[index] : String(index + 1));
    const existingSeriesValues=Array.isArray(point.seriesValues) ? point.seriesValues : null;
    const seriesValues=existingSeriesValues || seriesConfigs.map((series,seriesIndex)=>{
      const numeric=Number(series.values[index]);
      if(!Number.isFinite(numeric)) return null;
      const lineColor=series.lineColor || series.pointStroke || colors.accent;
      const displayLabel=series.yFormatter ? series.yFormatter(numeric) : formatChartValue(numeric);
      return {
        label:series.label || `Series ${seriesIndex + 1}`,
        exactLabel:displayLabel,
        displayLabel,
        color:lineColor
      };
    }).filter(Boolean);

    const firstSeriesIndex=seriesValues.length ? seriesConfigs.findIndex(series=>Number.isFinite(Number(series.values[index]))) : -1;
    const firstPoint=firstSeriesIndex>=0 ? seriesPoints[firstSeriesIndex][index] : null;

    return {
      ...point,
      xExactLabel,
      summary:point.summary || xExactLabel,
      xPercent:Number.isFinite(Number(point.xPercent))
        ? Number(point.xPercent)
        : firstPoint
          ? (firstPoint.x / width) * 100
          : (pointCount===1 ? 50 : (index/Math.max(1,pointCount-1))*100),
      yPercent:Number.isFinite(Number(point.yPercent))
        ? Number(point.yPercent)
        : firstPoint
          ? (firstPoint.y / height) * 100
          : 50,
      seriesValues
    };
  });

  config.pointMeta=pointMeta;

  const state=getChartState(container);
  state.points=pointMeta;
  state.chartKey=container.id || container;
  state.seriesConfig=seriesConfigs;

  cacheChartRenderState(container,config,width,height);
  bindChartInteractions(container,config);
  applyChartState(container,config);
}

function renderHistoryCharts(trendData,latestTrace,fallbackMode,fallbackNBackLevel){
  latestHistoryChartContext={ stats:null, latestTrace };
  const chartSelection=ensureHistoryChartSelection(fallbackMode,fallbackNBackLevel);
  const historyMode=chartSelection.mode;
  const historyNBackLevel=chartSelection.nBackLevel;
  const dailyAccuracyPoints=Array.isArray(trendData?.accuracyPoints) ? trendData.accuracyPoints : [];
  const dailyResponsePoints=Array.isArray(trendData?.responsePoints) ? trendData.responsePoints : [];
  const dailyYears=new Set([...dailyAccuracyPoints,...dailyResponsePoints].map(point=>new Date(point.dayStart).getFullYear()));
  const includeYearInLabels=dailyYears.size>1;
  const hasTrendData=dailyAccuracyPoints.length>0 || dailyResponsePoints.length>0;

  if(hasTrendData){
    renderLineChart(accuracyTrendChart,{
      values:dailyAccuracyPoints.map(point=>point.value),
      xValues:dailyAccuracyPoints.map(point=>point.dayStart),
      xLabels:dailyAccuracyPoints.map(point=>formatChartDateLabel(point.dayStart,includeYearInLabels)),
      xDetailLabel:"Date",
      yDetailLabel:"Average daily accuracy",
      yMin:0,
      yMax:100,
      xAxisLabel:"Date",
      ariaLabel:"Accuracy trend chart",
      emptyMessage:"No session data is available yet.",
      yFormatter:value=>formatChartValue(value,"%"),
      yTickStep:10,
      maxXLabels:getDailyTrendLabelCount(dailyAccuracyPoints.length),
      floorAtZero:true,
      showPoints:dailyAccuracyPoints.length===1,
      pointRadius:3.8,
      pointHoverRadius:5.0,
      pointSelectedRadius:6.0,
      labelFontSize:12,
      axisLabelFontSize:12,
      margin:{ top:14, right:12, bottom:42, left:50 },
      interactive:false
    });

    const responseValues=dailyResponsePoints.map(point=>point.value);

    renderLineChart(responseTimeTrendChart,{
      values:responseValues,
      xValues:dailyResponsePoints.map(point=>point.dayStart),
      xLabels:dailyResponsePoints.map(point=>formatChartDateLabel(point.dayStart,includeYearInLabels)),
      xDetailLabel:"Date",
      yDetailLabel:"Average daily response time",
      xAxisLabel:"Date",
      ariaLabel:"Response time trend chart",
      emptyMessage:"No session data is available yet.",
      yFormatter:value=>formatChartValue(value," ms"),
      yTickMode:"niceMs",
      desiredYTickCount:8,
      maxXLabels:getDailyTrendLabelCount(dailyResponsePoints.length),
      floorAtZero:false,
      showPoints:dailyResponsePoints.length===1,
      pointRadius:3.8,
      pointHoverRadius:5.0,
      pointSelectedRadius:6.0,
      labelFontSize:11,
      axisLabelFontSize:11,
      margin:{ top:14, right:12, bottom:42, left:50 },
      interactive:false
    });
  }else{
    const emptyMessage=`No ${formatArithmeticModeLabel(historyMode)} ${formatNBackLevel(historyNBackLevel)} sessions saved yet. Finish a session at this level to see trends over time.`;
    clearChartInteractions(accuracyTrendChart);
    clearChartInteractions(responseTimeTrendChart);
    ensureChartSurface(accuracyTrendChart).innerHTML=`<div class="chart-empty">${escapeSvgText(emptyMessage)}</div>`;
    ensureChartSurface(responseTimeTrendChart).innerHTML=`<div class="chart-empty">${escapeSvgText(emptyMessage)}</div>`;
    if(accuracyTrendDetails){
      accuracyTrendDetails.hidden=true;
      accuracyTrendDetails.innerHTML="";
    }
    if(responseTimeTrendDetails){
      responseTimeTrendDetails.hidden=true;
      responseTimeTrendDetails.innerHTML="";
    }
  }

  renderLatestIntervalChart(latestTrace);
}

function renderHistoryChartsSection(trendData,latestTrace,fallbackMode,fallbackNBackLevel){
  renderHistoryCharts(trendData,latestTrace,fallbackMode,fallbackNBackLevel);
}

function formatHistoryPageSummary(pageData){
  const totalSessions=Number(pageData?.totalSessions)||0;
  if(!totalSessions) return "Showing 0 sessions";
  const visibleStart=Number(pageData?.visibleStart)||0;
  const visibleEnd=Number(pageData?.visibleEnd)||0;
  return `Showing ${visibleStart}-${visibleEnd} of ${totalSessions} sessions`;
}

function formatHistoryPageIndicator(pageData){
  const pageCount=Number(pageData?.pageCount)||0;
  const pageIndex=Number(pageData?.pageIndex)||0;
  if(!pageCount) return "Page 0 of 0";
  return `Page ${pageIndex + 1} of ${pageCount}`;
}

function setHistoryStatsGlossaryVisible(isVisible){
  if(!historyStatsGlossary || !historyStatsInfoBtn) return;
  historyStatsGlossary.classList.toggle("hidden",!isVisible);
  historyStatsInfoBtn.setAttribute("aria-expanded",String(!!isVisible));
}

function setHistoryStatsGlossaryPinned(isPinned){
  historyStatsGlossaryPinned=!!isPinned;
  if(historyStatsHelp){
    historyStatsHelp.classList.toggle("tooltip-pinned",historyStatsGlossaryPinned);
  }
}

function closeHistoryStatsGlossary(){
  setHistoryStatsGlossaryPinned(false);
  setHistoryStatsGlossaryVisible(false);
}

function syncThresholdInfoAria(){
  if(!thresholdHelp || !thresholdInfoBtn) return;
  const advancedSettingsVisible=!advancedSettingsPanel || !advancedSettingsPanel.classList.contains("hidden");
  const isVisible=advancedSettingsVisible && (thresholdHelp.classList.contains("tooltip-pinned")
    || thresholdInfoBtn.matches(":hover"));
  thresholdInfoBtn.setAttribute("aria-expanded",String(isVisible));
}

function syncNBackInfoAria(){
  if(!nBackHelp || !nBackInfoBtn) return;
  const advancedSettingsVisible=!advancedSettingsPanel || !advancedSettingsPanel.classList.contains("hidden");
  const isVisible=advancedSettingsVisible && (nBackHelp.classList.contains("tooltip-pinned")
    || nBackInfoBtn.matches(":hover"));
  nBackInfoBtn.setAttribute("aria-expanded",String(isVisible));
}

function syncProfileInfoAria(){
  if(!profileHelp || !profileInfoBtn) return;
  const isVisible=profileHelp.classList.contains("tooltip-pinned") || profileInfoBtn.matches(":hover");
  profileInfoBtn.setAttribute("aria-expanded",String(isVisible));
}

function updateHistoryPaginationControls(pageData){
  const pageCount=Number(pageData?.pageCount)||0;
  if(historyPaginationSummary){
    historyPaginationSummary.textContent=formatHistoryPageSummary(pageData);
  }
  if(historyPaginationIndicator){
    historyPaginationIndicator.textContent=formatHistoryPageIndicator(pageData);
  }
  if(historyPaginationControls){
    historyPaginationControls.classList.toggle("is-single-page",pageCount<=1);
  }
  if(historyPrevPageBtn){
    historyPrevPageBtn.disabled=!pageData?.hasPrevious;
  }
  if(historyNextPageBtn){
    historyNextPageBtn.disabled=!pageData?.hasNext;
  }
}

function applyHistoryTrendToggleState(button,includeInTrends){
  if(!button) return;
  button.dataset.included=includeInTrends ? "true" : "false";
  button.textContent=includeInTrends ? "Included in trends" : "Excluded from trends";
  button.setAttribute("aria-pressed",String(!!includeInTrends));
  button.classList.toggle("is-included",includeInTrends);
  button.classList.toggle("is-excluded",!includeInTrends);
}

async function toggleHistorySessionTrendInclusion(session,button){
  if(!session || !button) return;
  const nextIncludeInTrends=!session.includeInTrends;
  const previousIncludeInTrends=!!session.includeInTrends;
  applyHistoryTrendToggleState(button,nextIncludeInTrends);
  button.disabled=true;

  try{
    const updatedSession={
      ...session,
      includeInTrends:nextIncludeInTrends
    };
    const saved=await sessionHistoryStore.saveSession(updatedSession);
    session.includeInTrends=typeof saved?.includeInTrends==="boolean" ? saved.includeInTrends : nextIncludeInTrends;
    applyHistoryTrendToggleState(button,session.includeInTrends);
  }catch(e){
    session.includeInTrends=previousIncludeInTrends;
    applyHistoryTrendToggleState(button,previousIncludeInTrends);
  }finally{
    button.disabled=false;
  }
}

function renderHistorySessionsSection(viewData){
  const stats=viewData?.stats || EMPTY_HISTORY_STATS;
  const pageData=viewData?.pageData || createEmptyHistoryPageData();

  historyCompletedSessions.textContent=String(stats.completedSessions);
  historyCorrectAnswers.textContent=String(stats.totalCorrectAnswers);
  historyDurationTrained.textContent=formatDuration(stats.totalDurationMs);

  syncHistoryFilterControls();
  recentSessionsList.innerHTML="";
  updateHistoryPaginationControls(pageData);

  if(!pageData.totalSessions){
    const empty=document.createElement("div");
    empty.className="history-empty";
    empty.textContent=getActiveHistoryFilterCount() ? "No sessions match the current filters." : "No saved sessions yet.";
    recentSessionsList.appendChild(empty);
    return;
  }

  if(!pageData.sessions.length){
    const empty=document.createElement("div");
    empty.className="history-empty";
    empty.textContent=getActiveHistoryFilterCount() ? "No sessions match the current filters." : "No saved sessions yet.";
    recentSessionsList.appendChild(empty);
    return;
  }

  pageData.sessions.forEach(session=>{
    const item=document.createElement("div");
    item.className="history-item";

    const top=document.createElement("div");
    top.className="history-item-top";

    const date=document.createElement("div");
    date.className="history-item-date";
    date.textContent=formatSessionDateTime(session.endedAt || session.startedAt);

    const status=document.createElement("span");
    status.className="history-status " + (session.status==="Manually exited" ? "manual" : "completed");
    status.textContent=session.status;

    top.appendChild(date);
    top.appendChild(status);

    const statsGrid=document.createElement("div");
    statsGrid.className="history-item-stats";

    const totalQuestionsAsked=Number(session.totalQuestionsAsked)||0;
    const correctAnswers=Number(session.correctAnswers)||0;
    const historyStatisticDefinitions=[
      {
        label:"Accuracy",
        value:formatPercent(Number(session.accuracy)||0),
        accessibleLabel:"Accuracy"
      },
      {
        label:"Median RT",
        value:formatHistoryResponseTimeStatistic(session.medianResponseTimeMs),
        accessibleLabel:"Median correct response time"
      },
      {
        label:"RT IQR",
        value:formatHistoryResponseTimeStatistic(session.responseTimeIqrMs),
        accessibleLabel:"Correct response-time interquartile range"
      },
      {
        label:"Average RT",
        value:Math.round(Number(session.averageResponseTimeMs)||0) + " ms",
        accessibleLabel:"Average response time"
      },
      {
        label:"Correct",
        value:correctAnswers + " / " + totalQuestionsAsked,
        accessibleLabel:"Correct answers out of total questions"
      },
      {
        label:"Duration",
        value:formatDuration(Number(session.durationMs)||0),
        accessibleLabel:"Session duration"
      }
    ];

    historyStatisticDefinitions.forEach(statistic=>{
      const stat=document.createElement("div");
      stat.className="history-item-stat";
      stat.setAttribute("role","group");
      stat.setAttribute("aria-label",statistic.accessibleLabel + ": " + statistic.value);

      const label=document.createElement("span");
      label.className="history-item-stat-label";
      label.textContent=statistic.label;

      const value=document.createElement("strong");
      value.className="history-item-stat-value";
      value.textContent=statistic.value;

      stat.appendChild(label);
      stat.appendChild(value);
      statsGrid.appendChild(stat);
    });

    const details=document.createElement("div");
    details.className="history-item-details";

    const detailsText=[
      formatArithmeticModeLabel(session.arithmeticMode || defaultSettings.mode),
      formatNBackLevel(session.nBackLevel),
      (session.endCondition || defaultSettings.endCondition) === "correct" ? "Correct-answer goal" : "Timer",
      "Thresholds " + formatThresholdSummary(Number(session.correctThreshold)||4, Number(session.incorrectThreshold)||4)
    ];
    detailsText.forEach((text,index)=>{
      const detail=document.createElement("span");
      detail.className="history-item-detail";
      detail.textContent=text;
      details.appendChild(detail);
      if(index<detailsText.length-1){
        const separator=document.createElement("span");
        separator.className="history-item-detail-separator";
        separator.setAttribute("aria-hidden","true");
        separator.textContent="•";
        details.appendChild(separator);
      }
    });

    const metadataRow=document.createElement("div");
    metadataRow.className="history-item-metadata-row";

    const trendRow=document.createElement("div");
    trendRow.className="history-item-trend";

    const trendButton=document.createElement("button");
    trendButton.type="button";
    trendButton.className="history-trend-toggle";
    trendButton.setAttribute("aria-label","Toggle whether this session contributes to trend graphs");
    applyHistoryTrendToggleState(trendButton,session.includeInTrends!==false);
    trendButton.onclick=()=>{
      void toggleHistorySessionTrendInclusion(session,trendButton);
    };

    trendRow.appendChild(trendButton);

    item.appendChild(top);
    item.appendChild(statsGrid);
    metadataRow.appendChild(details);
    metadataRow.appendChild(trendRow);

    item.appendChild(metadataRow);
    recentSessionsList.appendChild(item);
  });
}

function renderLatestIntervalChart(latestTrace){
  const tracePoints=Array.isArray(latestTrace?.trace) ? latestTrace.trace : [];
  syncLatestIntervalChartSession(latestTrace);

  if(!tracePoints.length){
    renderLatestIntervalChartEmptyState("No recent session data is available yet.");
    return;
  }

  const overviewData=buildLatestIntervalOverviewBlocks(tracePoints,latestIntervalChart?.clientWidth || 720);
  const detailBlockIndex=latestIntervalChartViewState.mode==="detail" ? latestIntervalChartViewState.blockIndex : null;
  const detailBlock=detailBlockIndex===null ? null : overviewData.blocks[detailBlockIndex];

  if(latestIntervalChartViewState.mode==="detail" && !detailBlock){
    setLatestIntervalChartMode("overview",null);
  }

  if(overviewData.blockSize===1){
    renderLatestIntervalChartRaw(latestTrace);
    return;
  }

  if(latestIntervalChartViewState.mode==="detail" && detailBlock){
    renderLatestIntervalChartDetail(latestTrace,detailBlock);
    return;
  }

  renderLatestIntervalChartOverview(latestTrace,overviewData);
}

function renderHistoryView(viewData){
  const stats=viewData?.stats || EMPTY_HISTORY_STATS;
  const latestTrace=viewData?.latestTrace || null;
  const pageData=viewData?.pageData || createEmptyHistoryPageData();
  const trendData=viewData?.trendData || createEmptyTrendData();
  const fallbackMode=viewData?.fallbackMode || defaultSettings.mode;
  const fallbackNBackLevel=normalizeNBackLevel(viewData?.fallbackNBackLevel);

  renderHistoryChartsSection(trendData,latestTrace,fallbackMode,fallbackNBackLevel);
  renderHistorySessionsSection({ stats, pageData });
}

async function refreshHistoryTrendCharts(){
  const refreshToken=++historyTrendRefreshToken;
  try{
    await sessionHistoryStore.waitForWrites();
    const [latestTrace,fallbackSettings]=await Promise.all([
      sessionHistoryStore.getLatestTrace(),
      sessionHistoryStore.getMostRecentHistorySettings()
    ]);
    const chartSelection=ensureHistoryChartSelection(fallbackSettings.mode,fallbackSettings.nBackLevel);
    const trendData=await sessionHistoryStore.getTrendData(chartSelection.mode,chartSelection.nBackLevel);
    if(refreshToken!==historyTrendRefreshToken) return;
    renderHistoryChartsSection(trendData,latestTrace,fallbackSettings.mode,fallbackSettings.nBackLevel);
  }catch(e){
    if(refreshToken!==historyTrendRefreshToken) return;
    renderHistoryChartsSection(createEmptyTrendData(),null,defaultSettings.mode,defaultSettings.nBackLevel);
  }
}

async function refreshHistorySessions(){
  const refreshToken=++historySessionRefreshToken;
  const filtersSnapshot={ ...historyFilters };
  try{
    await sessionHistoryStore.waitForWrites();
    const [stats,pageData]=await Promise.all([
      sessionHistoryStore.getStats(),
      sessionHistoryStore.getSessionPage({
        filters:filtersSnapshot,
        pageIndex:historyPageIndex,
        pageSize:HISTORY_PAGE_SIZE
      })
    ]);
    if(refreshToken!==historySessionRefreshToken) return;
    historyPageIndex=pageData.pageIndex;
    renderHistorySessionsSection({ stats, pageData });
  }catch(e){
    if(refreshToken!==historySessionRefreshToken) return;
    historyPageIndex=0;
    renderHistorySessionsSection({
      stats:EMPTY_HISTORY_STATS,
      pageData:createEmptyHistoryPageData()
    });
  }
}

async function refreshHistoryView(){
  const trendRefreshToken=++historyTrendRefreshToken;
  const sessionRefreshToken=++historySessionRefreshToken;
  const filtersSnapshot={ ...historyFilters };
  try{
    await sessionHistoryStore.waitForWrites();
    const [stats,latestTrace,fallbackSettings,pageData]=await Promise.all([
      sessionHistoryStore.getStats(),
      sessionHistoryStore.getLatestTrace(),
      sessionHistoryStore.getMostRecentHistorySettings(),
      sessionHistoryStore.getSessionPage({
        filters:filtersSnapshot,
        pageIndex:historyPageIndex,
        pageSize:HISTORY_PAGE_SIZE
      })
    ]);
    const chartSelection=ensureHistoryChartSelection(fallbackSettings.mode,fallbackSettings.nBackLevel);
    const trendData=await sessionHistoryStore.getTrendData(chartSelection.mode,chartSelection.nBackLevel);
    if(trendRefreshToken!==historyTrendRefreshToken || sessionRefreshToken!==historySessionRefreshToken) return;
    historyPageIndex=pageData.pageIndex;
    renderHistoryView({
      stats,
      latestTrace,
      trendData,
      pageData,
      fallbackMode:fallbackSettings.mode,
      fallbackNBackLevel:fallbackSettings.nBackLevel
    });
  }catch(e){
    if(trendRefreshToken!==historyTrendRefreshToken || sessionRefreshToken!==historySessionRefreshToken) return;
    historyPageIndex=0;
    renderHistoryView({
      stats:EMPTY_HISTORY_STATS,
      latestTrace:null,
      trendData:createEmptyTrendData(),
      pageData:createEmptyHistoryPageData(),
      fallbackMode:defaultSettings.mode,
      fallbackNBackLevel:defaultSettings.nBackLevel
    });
  }
}

function updateSessionLimitUI(correctAnswerCount=correctAnswers){
  if(endCondition==="correct"){
    sessionLimitLabel.textContent="Correct Answers";
    timeLeft.textContent=correctAnswerCount + " / " + targetCorrect;
    sessionLimitSuffix.textContent="";
    return;
  }

  sessionLimitLabel.textContent="Time Left";
  sessionLimitSuffix.textContent="s";
}

function initializeSessionLimitUI(durationMs){
  updateSessionLimitUI(0);
  if(endCondition==="timer"){
    timeLeft.textContent=String(Math.ceil(durationMs/1000));
  }
}

function applySessionTimerVisibility(isVisible){
  sessionTimerVisible=!!isVisible;
  const isTimerSession=endCondition==="timer";
  sessionTimerMetric.classList.toggle("hidden",isTimerSession&&!sessionTimerVisible);
  toggleSessionTimerBtn.classList.toggle("hidden",!isTimerSession);
  toggleSessionTimerBtn.setAttribute("aria-expanded",String(sessionTimerVisible));
  const actionLabel=sessionTimerVisible ? "Hide timer" : "Show timer";
  toggleSessionTimerBtn.setAttribute("aria-label",actionLabel);
  toggleSessionTimerBtn.title=actionLabel;
  toggleSessionTimerBtn.disabled=sessionState!=="active" || !isTimerSession;
}

function formatVoiceLabel(voiceKey){
  const normalized=normalizeVoiceKey(voiceKey);
  if(normalized==="samantha") return "Samantha";
  if(normalized==="nathan") return "Nathan";
  if(normalized==="enhancednathan") return "Enhanced Nathan";
  if(normalized==="siri4") return "Siri 4";

  const label=voiceKey
    .replace(/([a-zA-Z])(\d)/g,"$1 $2")
    .replace(/(\d)([a-zA-Z])/g,"$1 $2")
    .replace(/[-_]+/g," ")
    .replace(/\b\w/g,char=>char.toUpperCase());
  return label;
}

function normalizeVoiceEntry(voiceKey,entry){
  if(typeof entry==="string"){
    return {
      label:formatVoiceLabel(voiceKey),
      basePath:`audio/${voiceKey}`
    };
  }

  return {
    label:entry.label || formatVoiceLabel(voiceKey),
    basePath:entry.basePath || `audio/${voiceKey}`
  };
}

function mergeVoiceEntries(target,source){
  Object.entries(source||{}).forEach(([voiceKey,entry])=>{
    target[voiceKey]=normalizeVoiceEntry(voiceKey,entry);
  });
}

async function discoverVoices(){
  const discovered={};
  mergeVoiceEntries(discovered,window.CCT_VOICE_LIBRARY);

  if(!Object.keys(discovered).length){
    discovered.samantha={ label:"Samantha", basePath:"audio/samantha" };
    discovered.nathan={ label:"Nathan", basePath:"audio/nathan" };
    discovered.enhancednathan={ label:"Enhanced Nathan", basePath:"audio/enhancednathan" };
    discovered.siri4={ label:"Siri 4", basePath:"audio/siri4" };
  }

  voiceLibrary=discovered;
  return discovered;
}

async function refreshVoiceLibrary(){
  await discoverVoices();
  populateVoiceSelect();
}

function populateVoiceSelect(){
  const voices=Object.entries(voiceLibrary);
  voiceSelect.innerHTML="";

  voices.forEach(([voiceKey,voice])=>{
    const option=document.createElement("option");
    option.value=voiceKey;
    option.textContent=voice.label;
    voiceSelect.appendChild(option);
  });

  if(!voices.some(([voiceKey])=>voiceKey===selectedVoice)){
    selectedVoice=resolveVoiceKey(defaultSettings.voice,defaultSettings.voice);
  }
  voiceSelect.value=selectedVoice;
}

function getClockTime(){
  return window.performance&&window.performance.now?window.performance.now():Date.now();
}

function getVoiceConfig(voiceKey){
  const fallbackKey=Object.keys(voiceLibrary)[0];
  return voiceLibrary[voiceKey] || voiceLibrary[fallbackKey] || { label:formatVoiceLabel(defaultSettings.voice), basePath:`audio/${defaultSettings.voice}` };
}

function getVoiceClipUrl(voiceKey,num){
  const voice=getVoiceConfig(voiceKey);
  return `${voice.basePath}/${num}.mp3`;
}

function retainOnlyVoiceCache(voiceKey){
  Object.keys(voiceAudioCache).forEach(key=>{
    if(key!==voiceKey){
      delete voiceAudioCache[key];
    }
  });
}

function shouldPreloadAudio(){
  return window.location && window.location.protocol !== "file:";
}

function loadAudioClip(src){
  const audio=new Audio();
  audio.preload=shouldPreloadAudio() ? "auto" : "none";
  audio.src=src;
  if(shouldPreloadAudio()){
    audio.load();
  }
  return audio;
}

function preloadVoice(voiceKey){
  if(voiceAudioCache[voiceKey]?.ready) return Promise.resolve(voiceAudioCache[voiceKey]);
  if(voiceAudioCache[voiceKey]?.loading) return voiceAudioCache[voiceKey].loading;

  const entry=voiceAudioCache[voiceKey] || { clips:{}, ready:false, loading:null };
  const clipNumbers=[1,2,3,4,5,6,7,8,9];
  const clipPromises=clipNumbers.map(num=>new Promise(resolve=>{
    const audio=loadAudioClip(getVoiceClipUrl(voiceKey,num));
    entry.clips[num]=audio;
    let settled=false;
    const timeoutId=setTimeout(finish,1500);

    function finish(){
      if(settled) return;
      settled=true;
      clearTimeout(timeoutId);
      audio.removeEventListener("canplaythrough",finish);
      audio.removeEventListener("loadeddata",finish);
      audio.removeEventListener("error",finish);
      resolve(audio);
    }

    if(audio.readyState>=3){
      resolve(audio);
      return;
    }

    audio.addEventListener("canplaythrough",finish,{once:true});
    audio.addEventListener("loadeddata",finish,{once:true});
    audio.addEventListener("error",finish,{once:true});
  }));

  entry.loading=Promise.all(clipPromises).then(()=>{
    entry.ready=true;
    entry.loading=null;
    voiceAudioCache[voiceKey]=entry;
    return entry;
  });
  voiceAudioCache[voiceKey]=entry;
  return entry.loading;
}

async function testSelectedVoice(){
  if(voiceTestInProgress) return;
  const voice=resolveVoiceKey(voiceSelect.value || selectedVoice);
  if(!voice) return;

  voiceTestInProgress=true;
  const testButton=voiceTestBtn;
  if(testButton){
    testButton.disabled=true;
  }

  try{
    await preloadVoice(voice);
    const entry=voiceAudioCache[voice];
    const clipNumbers=entry && entry.clips ? Object.keys(entry.clips).map(Number).filter(Number.isFinite) : [];
    const clipNumber=clipNumbers.length ? clipNumbers[Math.floor(Math.random()*clipNumbers.length)] : 1;
    const template=entry && entry.clips && entry.clips[clipNumber];
    if(!template) return;

    stopStimulusAudioPlayback();

    const audio=template.cloneNode(true);
    audio.playbackRate=playbackSpeed;
    audio.currentTime=0;
    activeStimulusAudios.add(audio);

    const cleanup=()=>{
      activeStimulusAudios.delete(audio);
    };

    let resolvePlayback;
    const playbackDone=new Promise(resolve=>{
      resolvePlayback=resolve;
    });
    const settle=()=>{
      cleanup();
      resolvePlayback();
    };

    audio.addEventListener("ended",settle,{once:true});
    audio.addEventListener("error",settle,{once:true});

    const playPromise=audio.play();
    if(playPromise&&typeof playPromise.catch==="function"){
      playPromise.catch(cleanup);
    }
    await playbackDone;
  }finally{
    voiceTestInProgress=false;
    if(testButton){
      testButton.disabled=false;
    }
  }
}

function stopStimulusAudioPlayback(){
  activeStimulusAudios.forEach(audio=>{
    try{
      audio.pause();
      audio.currentTime=0;
    }catch(e){}
  });
  activeStimulusAudios.clear();
}

function playStimulusAudio(num){
  const voice=resolveVoiceKey(selectedVoice);
  const entry=voiceAudioCache[voice] || voiceAudioCache[Object.keys(voiceAudioCache)[0]];
  const template=entry&&entry.clips&&entry.clips[num];
  if(!template) return;

  stopStimulusAudioPlayback();

  const audio=template.cloneNode(true);
  audio.playbackRate=playbackSpeed;
  audio.currentTime=0;
  activeStimulusAudios.add(audio);

  const cleanup=()=>{
    activeStimulusAudios.delete(audio);
  };

  audio.addEventListener("ended",cleanup,{once:true});
  audio.addEventListener("error",cleanup,{once:true});

  const playPromise=audio.play();
  if(playPromise&&typeof playPromise.catch==="function"){
    playPromise.catch(cleanup);
  }
}

function updateLatestTraceResponseTime(responseTime,traceIndex=sessionIntervalTrace.length-1){
  if(!sessionIntervalTrace.length) return;
  const index=Math.max(0,Math.min(sessionIntervalTrace.length-1,Math.floor(Number(traceIndex)||0)));
  const point=sessionIntervalTrace[index];
  if(!point) return;
  const numeric=Number(responseTime);
  if(!Number.isFinite(numeric)) return;
  point.responseTime=Math.max(0,numeric);
}

function playBeep(force=false){
  if(!force && !beepEnabled)return;
  const AudioContextCtor=window.AudioContext||window.webkitAudioContext;
  if(!AudioContextCtor) return;

  if(!beepAudioContext){
    beepAudioContext=new AudioContextCtor();
  }

  const ctx=beepAudioContext;
  if(ctx.state==="suspended" && typeof ctx.resume==="function"){
    void ctx.resume();
  }

  const o=ctx.createOscillator();
  const g=ctx.createGain();
  o.frequency.value=1200; g.gain.value=getBeepGain();
  o.connect(g); g.connect(ctx.destination);
  o.start(); o.stop(ctx.currentTime+0.12);
  o.onended=()=>{
    try{
      o.disconnect();
      g.disconnect();
    }catch(e){}
  };
}

async function closeBeepAudioContext(){
  if(!beepAudioContext) return;
  const ctx=beepAudioContext;
  beepAudioContext=null;
  try{
    if(typeof ctx.close==="function" && ctx.state!=="closed"){
      await ctx.close();
    }
  }catch(e){}
}

function getRandomNumber(){return Math.floor(Math.random()*9)+1;}

function updateFeedbackUI(){
  const fb=document.getElementById("feedback"); fb.innerHTML="";
  const slotCount=getIndicatorSlotCount();
  for(let i=0;i<slotCount;i++){
    const d=document.createElement("span");
    const active=i<feedbackIndicatorCount;
    d.className=`dot feedback-slot ${active?feedbackIndicatorColor:"empty"}`;
    fb.appendChild(d);
  }
}

function resetFeedbackIndicators(){
  feedbackIndicatorColor=null;
  feedbackIndicatorCount=0;
  updateFeedbackUI();
}

function setFeedbackIndicators(color,count){
  feedbackIndicatorColor=color;
  feedbackIndicatorCount=Math.max(0,Math.min(getIndicatorSlotCount(),count));
  updateFeedbackUI();
}

function tickIntervalTime(){
  intervalStatsTimerId=null;
  if(!gameRunning) return;
  if(!showIntervalTiming) return;

  const now=getClockTime();

  if(interval !== startingInterval || intervalCounts[interval]){
    intervalTime[interval]=(intervalTime[interval]||0)+(now-currentIntervalStart);
  }

  currentIntervalStart=now;
  updateIntervalStats();

  intervalStatsTimerId=setTimeout(tickIntervalTime,100);
}

function getSortedIntervalKeys(){
  if(intervalKeysDirty){
    sortedIntervalKeys=Object.keys(intervalCounts).sort((a,b)=>b-a);
    intervalKeysDirty=false;
  }
  return sortedIntervalKeys;
}

function renderIntervalStatsInto(target){
  if(!target) return;
  const keys=getSortedIntervalKeys();

  keys.forEach((key,index)=>{
    const time=(intervalTime[key]||0)/1000;
    const text=key + "ms: " + intervalCounts[key] + "  —  " + time.toFixed(1) + "s";
    let row=target.children[index];
    if(!row){
      row=document.createElement("div");
      target.appendChild(row);
    }
    if(row.textContent!==text){
      row.textContent=text;
    }
  });

  while(target.children.length>keys.length){
    target.lastElementChild.remove();
  }
}

function updateIntervalStats(){
  if(!showIntervalTiming){
    intervalStats.innerHTML="";
    if(resultsIntervalStats){
      resultsIntervalStats.innerHTML="";
    }
    return;
  }

  renderIntervalStatsInto(intervalStats);
  if(!gameRunning){
    renderIntervalStatsInto(resultsIntervalStats);
  }
}

function getThresholds(){
  return {
    correct:parsePositiveInteger(correctThresholdInput.value,defaultSettings.correctThreshold),
    incorrect:parsePositiveInteger(incorrectThresholdInput.value,defaultSettings.incorrectThreshold)
  };
}

function updateIntervalInputConstraints(){
  const step=clampInteger(intervalIncrementSelect.value,parseInt(defaultSettings.intervalIncrement,10),10,100);

  maximumIntervalInput.min=String(MIN_INTERVAL_VALUE);
  maximumIntervalInput.max=String(MAX_INTERVAL_VALUE);
  maximumIntervalInput.step=String(step);
  startingIntervalInput.min=String(MIN_INTERVAL_VALUE);
  startingIntervalInput.max=String(MAX_INTERVAL_VALUE);
  startingIntervalInput.step=String(step);
  minimumIntervalInput.min=String(MIN_INTERVAL_VALUE);
  minimumIntervalInput.max=String(MAX_INTERVAL_VALUE);
  minimumIntervalInput.step=String(step);
}

function getIntervalInputBounds(input){
  return {
    min:MIN_INTERVAL_VALUE,
    max:MAX_INTERVAL_VALUE
  };
}

function rememberIntervalInputValue(input){
  input.dataset.lastAcceptedValue=input.value;
}

function parseIntervalInputValue(value){
  if(String(value).trim()==="") return null;
  const parsed=Number(value);
  if(!Number.isInteger(parsed) || !Number.isFinite(parsed)) return null;
  if(parsed<MIN_INTERVAL_VALUE || parsed>MAX_INTERVAL_VALUE) return null;
  return parsed;
}

function getIntervalFallbackValue(fallback){
  const parsed=parseIntervalInputValue(fallback);
  return parsed===null ? MIN_INTERVAL_VALUE : parsed;
}

function readIntervalInputValue(input,fallback){
  const value=parseIntervalInputValue(input.value);
  if(value!==null) return value;

  const previous=parseIntervalInputValue(input.dataset.lastAcceptedValue);
  if(previous!==null) return previous;
  return getIntervalFallbackValue(fallback);
}

function getDefaultIntervalInputValue(input){
  if(input===startingIntervalInput) return parseInt(defaultSettings.startingInterval,10);
  if(input===maximumIntervalInput) return parseInt(defaultSettings.maximumInterval,10);
  return parseInt(defaultSettings.minimumInterval,10);
}

function restoreInvalidIntervalInput(input){
  input.value=String(readIntervalInputValue(input,getDefaultIntervalInputValue(input)));
}

function reconcileIntervalInputs(changedInput=null){
  if(changedInput){
    const changedValue=parseIntervalInputValue(changedInput.value);
    if(changedValue===null){
      restoreInvalidIntervalInput(changedInput);
      return false;
    }
  }

  let minimum=readIntervalInputValue(minimumIntervalInput,parseInt(defaultSettings.minimumInterval,10));
  let starting=readIntervalInputValue(startingIntervalInput,parseInt(defaultSettings.startingInterval,10));
  let maximum=readIntervalInputValue(maximumIntervalInput,parseInt(defaultSettings.maximumInterval,10));
  if(changedInput===minimumIntervalInput){
    minimum=parseIntervalInputValue(changedInput.value);
  }else if(changedInput===startingIntervalInput){
    starting=parseIntervalInputValue(changedInput.value);
  }else if(changedInput===maximumIntervalInput){
    maximum=parseIntervalInputValue(changedInput.value);
  }
  maximum=Math.max(maximum,minimum,starting);
  starting=Math.max(minimum,Math.min(starting,maximum));
  if(changedInput===maximumIntervalInput){
    maximum=parseIntervalInputValue(changedInput.value);
    minimum=Math.min(minimum,maximum);
    starting=Math.min(starting,maximum);
  }else if(changedInput===minimumIntervalInput){
    minimum=parseIntervalInputValue(changedInput.value);
    starting=Math.max(starting,minimum);
    maximum=Math.max(maximum,starting);
  }else if(changedInput===startingIntervalInput){
    starting=parseIntervalInputValue(changedInput.value);
    minimum=Math.min(minimum,starting);
    maximum=Math.max(maximum,starting);
  }

  minimum=Math.max(MIN_INTERVAL_VALUE,Math.min(MAX_INTERVAL_VALUE,minimum));
  maximum=Math.max(minimum,Math.min(MAX_INTERVAL_VALUE,maximum));
  starting=Math.max(minimum,Math.min(maximum,starting));

  minimumIntervalInput.value=String(minimum);
  startingIntervalInput.value=String(starting);
  maximumIntervalInput.value=String(maximum);
  rememberIntervalInputValue(minimumIntervalInput);
  rememberIntervalInputValue(startingIntervalInput);
  rememberIntervalInputValue(maximumIntervalInput);

  return true;
}

function validateIntervalInput(input){
  const isValid=reconcileIntervalInputs(input);
  if(isValid){
    saveSettings();
  }
  return isValid;
}

function stepIntervalInput(inputId,direction){
  const input=document.getElementById(inputId);
  if(!input) return;

  const step=clampInteger(intervalIncrementSelect.value,parseInt(defaultSettings.intervalIncrement,10),10,100);
  const current=parseIntervalInputValue(input.value);
  if(current===null){
    restoreInvalidIntervalInput(input);
    return;
  }

  const delta=direction==="up" ? step : -step;
  const bounds=getIntervalInputBounds(input);
  const next=Math.max(bounds.min,Math.min(bounds.max,current+delta));
  if(next===current) return;

  input.value=String(next);
  input.dispatchEvent(new Event("change",{ bubbles:true }));
}

function changeInterval(newInterval){
  const clampedInterval=Math.max(minimumInterval,Math.min(maximumInterval,newInterval));
  if(clampedInterval===interval){
    resetFeedbackIndicators();
    return;
  }

  const now=getClockTime();
  const previousInterval=interval;

  if(showIntervalTiming){
    if(previousInterval !== startingInterval || intervalCounts[previousInterval]){
      intervalTime[previousInterval]=(intervalTime[previousInterval]||0)+(now-currentIntervalStart);
    }
  }

  interval=clampedInterval;
  if(showIntervalTiming){
    currentIntervalStart=now;

    if(!Object.prototype.hasOwnProperty.call(intervalCounts,interval)){
      intervalKeysDirty=true;
    }
    intervalCounts[interval]=(intervalCounts[interval]||0)+1;

    updateIntervalStats();
  }
  resetFeedbackIndicators();

  if(gameRunning&&!isStimulusTick){
    scheduleNextStimulusFromLastStimulus();
  }
}

function adjustDifficulty(){
  const t=getThresholds();

  if(correctStreak>=t.correct){
    changeInterval(interval-intervalIncrement);
    correctStreak=0;
  }

  if(wrongStreak>=t.incorrect){
    changeInterval(interval+intervalIncrement);
    wrongStreak=0;
  }

  document.getElementById("currentInterval").textContent=interval;
}

function recordScoredItem(isCorrect,responseTime,traceIndex=sessionIntervalTrace.length-1){
  scoredItemCount++;
  const normalizedResponseTime=Math.max(0,responseTime);
  totalResponseTime+=normalizedResponseTime;
  if(isCorrect){
    correctResponseTimes.push(normalizedResponseTime);
  }
  if(isCorrect) correctAnswers++;
  updateLatestTraceResponseTime(responseTime,traceIndex);
}

function clearPendingAnswer(){
  awaitingAnswer=false;
  responseStartedAt=0;
  responseInterval=0;
  answer.value="";
}

function resetQuestionStates(){
  activeQuestionState=null;
}

function hasEnoughStimuliForQuestion(){
  return stimulusHistory.length >= nBackLevel + 1;
}

function createQuestionState(startedAt){
  const traceIndex=Math.max(0,sessionIntervalTrace.length-1);
  const latestIndex=stimulusHistory.length-1;
  const nBackNumber=stimulusHistory[latestIndex-nBackLevel];
  const latestNumber=stimulusHistory[latestIndex];
  return {
    startedAt,
    responseInterval:interval,
    expectedAnswer:hasEnoughStimuliForQuestion() ? getExpectedAnswer(nBackNumber,latestNumber) : null,
    traceIndex,
    resolved:false
  };
}

function finalizeQuestionState(questionState,submittedValue,finalizedAt){
  if(!questionState || questionState.resolved) return false;

  const resolvedAt=Number.isFinite(Number(finalizedAt)) ? Number(finalizedAt) : getClockTime();
  const isCorrect=isCorrectAnswerInput(questionState,submittedValue,resolvedAt);
  const responseTime=isCorrect
    ? Math.min(Math.max(0,questionState.startedAt ? resolvedAt-questionState.startedAt : 0),questionState.responseInterval || interval)
    : (questionState.responseInterval || interval);

  questionState.resolved=true;

  if(questionState===activeQuestionState){
    clearPendingAnswer();
  }

  recordScoredItem(isCorrect,responseTime,questionState.traceIndex);

  if(isCorrect){
    setFeedbackIndicators("green",correctStreak+1);
    correctStreak++;
    wrongStreak=0;
    adjustDifficulty();
    updateSessionLimitUI();
    if(endCondition==="correct"&&correctAnswers>=targetCorrect){
      stopGame("completed");
    }
  }else{
    setFeedbackIndicators("red",wrongStreak+1);
    wrongStreak++;
    correctStreak=0;
    playBeep();
    adjustDifficulty();
  }

  return isCorrect;
}

function isCorrectAnswerInput(questionState,submittedValue,finalizedAt){
  if(!questionState || questionState.resolved) return false;

  const normalizedValue=String(submittedValue ?? "").trim();
  return normalizedValue!==""
    && questionState.expectedAnswer!==null
    && normalizedValue===String(questionState.expectedAnswer);
}

function isAllowedSessionClick(target){
  return target===answer || answer.contains(target)
    || target===endSessionBtn || endSessionBtn.contains(target)
    || target===toggleSessionTimerBtn || toggleSessionTimerBtn.contains(target);
}

function restoreAnswerFocus(){
  if(sessionState!=="active") return;
  if(document.activeElement===answer) return;
  try{
    answer.focus({ preventScroll:true });
  }catch(e){
    answer.focus();
  }
}

function formatPercent(value){
  return value.toFixed(1).replace(/\.0$/,"") + "%";
}

function formatDuration(ms){
  if(ms<10000){
    const seconds=(ms/1000).toFixed(1).replace(/\.0$/,"");
    return seconds + "s";
  }

  const totalSeconds=Math.round(ms/1000);
  const minutes=Math.floor(totalSeconds/60);
  const seconds=totalSeconds%60;

  if(minutes===0) return seconds + "s";
  return minutes + "m " + seconds + "s";
}

function formatResponseTimeStatistic(value){
  const normalized=normalizeOptionalNonNegativeNumber(value);
  return normalized===null ? "N/A" : Math.round(normalized) + " ms";
}

function formatHistoryResponseTimeStatistic(value){
  const normalized=normalizeOptionalNonNegativeNumber(value);
  return normalized===null ? "—" : Math.round(normalized) + " ms";
}

function formatCsvTimestamp(value){
  const timestamp=Number(value);
  if(!Number.isFinite(timestamp) || timestamp<=0) return "";
  const date=new Date(timestamp);
  return Number.isFinite(date.getTime()) ? date.toISOString() : "";
}

function formatExportFileDate(date=new Date()){
  const year=date.getFullYear();
  const month=String(date.getMonth()+1).padStart(2,"0");
  const day=String(date.getDate()).padStart(2,"0");
  return `${year}-${month}-${day}`;
}

function escapeCsvCell(value){
  if(value===null || value===undefined) return "";
  const text=String(value);
  const safeText=typeof value==="string" && /^\s*[=+\-@]/.test(text)
    ? "'" + text
    : text;
  return /[",\r\n]/.test(safeText) ? `"${safeText.replace(/"/g,'""')}"` : safeText;
}

function buildSessionHistoryCsv(sessions){
  const columns=[
    { header:"sessionId", getValue:session=>session.sessionId },
    { header:"startedAt", getValue:session=>formatCsvTimestamp(session.startedAt) },
    { header:"endedAt", getValue:session=>formatCsvTimestamp(session.endedAt) },
    { header:"status", getValue:session=>session.status },
    { header:"arithmeticMode", getValue:session=>session.arithmeticMode },
    { header:"nBackLevel", getValue:session=>session.nBackLevel },
    { header:"endCondition", getValue:session=>session.endCondition },
    { header:"durationMs", getValue:session=>session.durationMs },
    { header:"accuracyPercent", getValue:session=>session.accuracy },
    { header:"correctAnswers", getValue:session=>session.correctAnswers },
    { header:"totalQuestionsAsked", getValue:session=>session.totalQuestionsAsked },
    { header:"averageResponseTimeMs", getValue:session=>session.averageResponseTimeMs },
    { header:"medianResponseTimeMs", getValue:session=>session.medianResponseTimeMs },
    { header:"responseTimeIqrMs", getValue:session=>session.responseTimeIqrMs },
    { header:"correctThreshold", getValue:session=>session.correctThreshold },
    { header:"incorrectThreshold", getValue:session=>session.incorrectThreshold },
    { header:"startingInterval", getValue:session=>session.startingInterval },
    { header:"maximumInterval", getValue:session=>session.maximumInterval },
    { header:"minimumInterval", getValue:session=>session.minimumInterval },
    { header:"intervalIncrement", getValue:session=>session.intervalIncrement },
    { header:"voice", getValue:session=>session.voice },
    { header:"playbackSpeed", getValue:session=>session.playbackSpeed },
    { header:"includeInTrends", getValue:session=>session.includeInTrends }
  ];
  const rows=[columns.map(column=>escapeCsvCell(column.header)).join(",")];
  (Array.isArray(sessions) ? sessions : []).forEach(session=>{
    rows.push(columns.map(column=>escapeCsvCell(column.getValue(session))).join(","));
  });
  return rows.join("\r\n") + "\r\n";
}

function renderResults(responseTimeStats){
  const totalItems=scoredItemCount;
  const accuracy=totalItems?correctAnswers/totalItems*100:0;
  const averageResponseTime=totalItems?totalResponseTime/totalItems:0;
  const duration=Math.max(0,sessionEndedAt-sessionStartedAt);
  const totalQuestionsAsked=Math.max(0,totalItems);

  resultAccuracy.textContent=formatPercent(accuracy);
  resultAverageResponse.textContent=Math.round(averageResponseTime) + " ms";
  resultMedianResponse.textContent=formatResponseTimeStatistic(responseTimeStats.medianResponseTimeMs);
  resultResponseTimeIqr.textContent=formatResponseTimeStatistic(responseTimeStats.responseTimeIqrMs);
  resultDuration.textContent=formatDuration(duration);
  resultCorrect.textContent=correctAnswers.toString();
  resultQuestions.textContent=totalQuestionsAsked.toString();
  resultStatus.textContent=sessionOutcome;
}

function scheduleNextStimulus(delay=interval){
  if(!gameRunning)return;

  const scheduleSerial=++stimulusScheduleSerial;
  clearTimeout(timeoutId);
  timeoutId=setTimeout(()=>{
    if(!gameRunning || scheduleSerial!==stimulusScheduleSerial) return;
    runStimulus();
  },Math.max(0,delay));
}

function scheduleNextStimulusFromLastStimulus(){
  if(!gameRunning) return;
  const anchorAt=lastStimulusAt || getClockTime();
  scheduleNextStimulus((anchorAt + interval) - getClockTime());
}

function startStimulusScheduler(){
  lastStimulusAt=getClockTime()-interval;
  scheduleNextStimulusFromLastStimulus();
}

function runStimulus(){
  if(!gameRunning)return;

  isStimulusTick=true;

  const expiredQuestionState=activeQuestionState;
  if(expiredQuestionState && !expiredQuestionState.resolved){
    finalizeQuestionState(expiredQuestionState,answer.value,getClockTime());
  }

  const num=getRandomNumber();
  const now=getClockTime();
  lastStimulusAt=now;
  clearPendingAnswer();
  stimulusHistory.push(num);
  if(stimulusHistory.length>nBackLevel+1){
    stimulusHistory.shift();
  }
  stimulusCount++;
  sessionIntervalTrace.push({
    questionNumber:stimulusCount,
    interval,
    timestamp:now,
    responseTime:null
  });
  playStimulusAudio(num);

  if(hasEnoughStimuliForQuestion()){
    awaitingAnswer=true;
    responseStartedAt=now;
    responseInterval=interval;
    activeQuestionState=createQuestionState(now);
  }else{
    clearPendingAnswer();
    activeQuestionState=null;
  }

  isStimulusTick=false;
  if(gameRunning){
    scheduleNextStimulusFromLastStimulus();
  }
}

function updateTimer(){
  countdownTimerId=null;
  if(!gameRunning||endCondition!=="timer")return;
  const remainingMs=endTime-Date.now();
  const r=Math.max(0,Math.ceil(remainingMs/1000));
  const displayValue=String(r);
  if(timeLeft.textContent!==displayValue){
    timeLeft.textContent=displayValue;
  }
  if(remainingMs<=0){
    stopGame("completed");
    return;
  }

  const nextBoundaryDelay=remainingMs-((r-1)*1000)+1;
  countdownTimerId=setTimeout(updateTimer,Math.max(1,Math.min(1000,nextBoundaryDelay)));
}

async function startGame(){
  if(sessionState!=="idle") return;

  reconcileIntervalInputs();
  saveSettings();
  currentSessionId=generateSessionId();

  const minimumIntervalCandidate=Math.max(MIN_INTERVAL_VALUE,parseInt(minimumIntervalInput.value)||parseInt(defaultSettings.minimumInterval));
  const startingIntervalCandidate=Math.max(MIN_INTERVAL_VALUE,parseInt(startingIntervalInput.value)||parseInt(defaultSettings.startingInterval));
  const maximumIntervalCandidate=Math.max(MIN_INTERVAL_VALUE,parseInt(maximumIntervalInput.value)||parseInt(defaultSettings.maximumInterval));
  minimumInterval=minimumIntervalCandidate;
  maximumInterval=Math.max(minimumIntervalCandidate,startingIntervalCandidate,maximumIntervalCandidate);
  startingInterval=Math.max(minimumInterval,Math.min(startingIntervalCandidate,maximumInterval));
  interval=startingInterval;
  endCondition=endConditionSelect.value;
  targetCorrect=Math.max(1,parseInt(targetCorrectInput.value)||parseInt(defaultSettings.targetCorrect));
  applyArithmeticMode(modeSelect.value);
  nBackLevel=normalizeNBackLevel(nBackLevelInput.value);
  nBackLevelInput.value=String(nBackLevel);
  const duration=Math.max(1,parseInt(durationInput.value)||parseInt(defaultSettings.duration))*60000;
  beepEnabled=beepToggle.checked;
  showIntervalTiming=showIntervalTimingToggle.checked;
  selectedVoice=resolveVoiceKey(voiceSelect.value);
  voiceSelect.value=selectedVoice;
  playbackSpeed=parseFloat(playbackSpeedSelect.value)||1;
  currentInterval.textContent=startingInterval;
  initializeSessionLimitUI(duration);
  sessionTimerVisible=!hideTimerDuringSession;
  applySessionTimerVisibility(sessionTimerVisible);
  setSessionState("starting");
  await preloadVoice(selectedVoice);
  if(sessionState!=="starting") return;
  retainOnlyVoiceCache(selectedVoice);

  scoredItemCount=0;
  totalResponseTime=0;
  correctResponseTimes=[];
  stimulusCount=0;
  stimulusHistory=[];
  correctStreak=0; wrongStreak=0;
  correctAnswers=0;
  excludeLastQuestionFromTrace=false;
  sessionOutcome="Completed";
  intervalCounts={}; intervalTime={};
  sortedIntervalKeys=[];
  intervalKeysDirty=true;
  sessionIntervalTrace=[];
  resetQuestionStates();
  resetFeedbackIndicators();
  applyIntervalTimingVisibility(showIntervalTiming);
  sessionStartedAt=Date.now();
  sessionEndedAt=0;
  responseStartedAt=0;
  responseInterval=0;

  gameRunning=false;
  awaitingAnswer=false;

  currentIntervalStart=showIntervalTiming?getClockTime():0;

  answer.value="";

  if(endCondition==="timer"){
    endTime=sessionStartedAt+duration;
  }else{
    endTime=0;
  }
  intervalStats.innerHTML="";
  updateFeedbackUI();

  timeoutId=setTimeout(()=>{
    if(sessionState!=="starting") return;

    gameRunning=true;
    setSessionState("active");
    answer.focus();

    startStimulusScheduler();
    if(endCondition==="timer") updateTimer();
    tickIntervalTime(); // START CONTINUOUS TRACKING
  },100);
}

function stopGame(reason="manual"){
  if(sessionState!=="active"&&sessionState!=="starting") return;

  sessionOutcome=reason==="manual" ? "Manually exited" : "Completed";
  excludeLastQuestionFromTrace=awaitingAnswer && activeQuestionState && answer.value.trim()==="";
  sessionEndedAt=Date.now();
  gameRunning=false;
  clearTimeout(timeoutId);
  if(intervalStatsTimerId!==null){
    clearTimeout(intervalStatsTimerId);
    intervalStatsTimerId=null;
  }
  if(countdownTimerId!==null){
    clearTimeout(countdownTimerId);
    countdownTimerId=null;
  }
  stopStimulusAudioPlayback();
  void closeBeepAudioContext();

  if(awaitingAnswer && activeQuestionState){
    if(answer.value.trim()===""){
      updateLatestTraceResponseTime(responseInterval||interval,activeQuestionState.traceIndex);
    }else{
      finalizeQuestionState(activeQuestionState,answer.value,getClockTime());
    }
  }
  clearPendingAnswer();

  answer.blur();
  resetQuestionStates();

  // finalize last interval
  if(showIntervalTiming && currentIntervalStart){
    const now=getClockTime();
    if(interval !== startingInterval || intervalCounts[interval]){
      intervalTime[interval]=(intervalTime[interval]||0)+(now-currentIntervalStart);
    }
  }

  updateIntervalStats();

  if(endCondition==="timer") timeLeft.textContent="0";
  const responseTimeStats=calculateResponseTimeStats(correctResponseTimes);
  renderResults(responseTimeStats);
  const sessionRecord=buildSessionRecord(responseTimeStats);
  const latestTraceRecord=buildLatestTraceRecord();
  correctResponseTimes=[];
  if(shouldStoreSession(sessionRecord)){
    void Promise.all([
      sessionHistoryStore.saveLatestTrace(latestTraceRecord),
      sessionHistoryStore.saveSession(sessionRecord)
    ]).catch(()=>{
      setProfileStatus("This browser could not save the session history.","error");
    });
  }
  setSessionState("results");
}

function checkInputLive(event){
  if(sessionState!=="active") return;
  if(!awaitingAnswer || !hasEnoughStimuliForQuestion() || !activeQuestionState || activeQuestionState.resolved) return;

  const submittedValue=answer.value.trim();
  if(submittedValue==="") return;

  if(isCorrectAnswerInput(activeQuestionState,submittedValue,getClockTime())){
    finalizeQuestionState(activeQuestionState,submittedValue,getClockTime());
  }
}

const startBtn=document.getElementById("startBtn");
const endSessionBtn=document.getElementById("endSessionBtn");
const newSessionBtn=document.getElementById("newSessionBtn");
const answer=document.getElementById("answer");
const startingIntervalInput=document.getElementById("startingInterval");
const maximumIntervalInput=document.getElementById("maximumInterval");
const minimumIntervalInput=document.getElementById("minimumInterval");
const durationInput=document.getElementById("duration");
const durationField=document.getElementById("durationField");
const intervalIncrementSelect=document.getElementById("intervalIncrement");
const intervalIncrementValue=document.getElementById("intervalIncrementValue");
const endConditionSelect=document.getElementById("endCondition");
const targetCorrectInput=document.getElementById("targetCorrect");
const targetCorrectField=document.getElementById("targetCorrectField");
const modeField=document.getElementById("modeField");
const modeSelect=document.getElementById("modeSelect");
const nBackLevelField=document.getElementById("nBackLevelField");
const nBackLevelInput=document.getElementById("nBackLevelInput");
const nBackHelp=document.querySelector(".n-back-help");
const nBackInfoBtn=document.getElementById("nBackInfoBtn");
const correctThresholdInput=document.getElementById("correctThreshold");
const incorrectThresholdInput=document.getElementById("incorrectThreshold");
const showAdvancedSettingsToggle=document.getElementById("showAdvancedSettingsToggle");
const advancedSettingsPanel=document.getElementById("advancedSettingsPanel");
const advancedSections=document.getElementById("advancedSections");
const normalThresholdPresetBtn=document.getElementById("normalThresholdPresetBtn");
const highAccuracyPresetBtn=document.getElementById("highAccuracyPresetBtn");
const thresholdHelp=document.querySelector(".threshold-help");
const thresholdInfoBtn=document.getElementById("thresholdInfoBtn");
const voiceSelect=document.getElementById("voiceSelect");
const voiceTestBtn=document.getElementById("voiceTestBtn");
const playbackSpeedSelect=document.getElementById("playbackSpeedSelect");
const beepVolumeField=document.getElementById("beepVolumeField");
const beepVolumeSelect=document.getElementById("beepVolume");
const beepVolumeValue=document.getElementById("beepVolumeValue");
const beepTestBtn=document.getElementById("beepTestBtn");
const beepToggle=document.getElementById("beepToggle");
const themeToggle=document.getElementById("themeToggle");
const showIntervalTimingToggle=document.getElementById("showIntervalTimingToggle");
const hideTimerDuringSessionToggle=document.getElementById("hideTimerDuringSessionToggle");
const resetSettingsBtn=document.getElementById("resetSettingsBtn");
const profileSelect=document.getElementById("profileSelect");
const newProfileBtn=document.getElementById("newProfileBtn");
const renameProfileBtn=document.getElementById("renameProfileBtn");
const deleteProfileBtn=document.getElementById("deleteProfileBtn");
const profileStatus=document.getElementById("profileStatus");
const profileHelp=document.querySelector(".profile-help");
const profileInfoBtn=document.getElementById("profileInfoBtn");
const profileNameDialog=document.getElementById("profileNameDialog");
const profileNameForm=document.getElementById("profileNameForm");
const profileNameDialogTitle=document.getElementById("profileNameDialogTitle");
const profileNameInput=document.getElementById("profileNameInput");
const profileSourceField=document.getElementById("profileSourceField");
const profileNameError=document.getElementById("profileNameError");
const cancelProfileNameBtn=document.getElementById("cancelProfileNameBtn");
const confirmProfileNameBtn=document.getElementById("confirmProfileNameBtn");
const confirmationDialog=document.getElementById("confirmationDialog");
const confirmationForm=document.getElementById("confirmationForm");
const confirmationDialogTitle=document.getElementById("confirmationDialogTitle");
const confirmationDialogMessage=document.getElementById("confirmationDialogMessage");
const cancelConfirmationBtn=document.getElementById("cancelConfirmationBtn");
const confirmConfirmationBtn=document.getElementById("confirmConfirmationBtn");
const playbackSpeedValue=document.getElementById("playbackSpeedValue");
const currentInterval=document.getElementById("currentInterval");
const timeLeft=document.getElementById("timeLeft");
const sessionLimitLabel=document.getElementById("sessionLimitLabel");
const sessionLimitSuffix=document.getElementById("sessionLimitSuffix");
const sessionTimerMetric=document.getElementById("sessionTimerMetric");
const toggleSessionTimerBtn=document.getElementById("toggleSessionTimerBtn");
const intervalStats=document.getElementById("intervalStats");
const resultsIntervalStatsWrap=document.getElementById("resultsIntervalStatsWrap");
const resultsIntervalStats=document.getElementById("resultsIntervalStats");
const sessionView=document.getElementById("sessionView");
const resultsView=document.getElementById("resultsView");
const resultAccuracy=document.getElementById("resultAccuracy");
const resultAverageResponse=document.getElementById("resultAverageResponse");
const resultMedianResponse=document.getElementById("resultMedianResponse");
const resultResponseTimeIqr=document.getElementById("resultResponseTimeIqr");
const resultDuration=document.getElementById("resultDuration");
const resultCorrect=document.getElementById("resultCorrect");
const resultQuestions=document.getElementById("resultQuestions");
const resultStatus=document.getElementById("resultStatus");
const settingsView=document.getElementById("settingsView");
const footerView=document.getElementById("footerView");
const historyView=document.getElementById("historyView");
const historyBtn=document.getElementById("historyBtn");
const clearSessionsOnlyBtn=document.getElementById("clearSessionsOnlyBtn");
const clearAllHistoryBtn=document.getElementById("clearAllHistoryBtn");
const historyStatsHelp=document.getElementById("historyStatsHelp");
const historyStatsInfoBtn=document.getElementById("historyStatsInfoBtn");
const historyStatsGlossary=document.getElementById("historyStatsGlossary");
const historyFilterBtn=document.getElementById("historyFilterBtn");
const historyFilterCountBadge=document.getElementById("historyFilterCountBadge");
const resetHistoryFiltersBtn=document.getElementById("resetHistoryFiltersBtn");
const backFromHistoryBtn=document.getElementById("backFromHistoryBtn");
const refreshTrendChartsBtn=document.getElementById("refreshTrendChartsBtn");
const refreshSessionsBtn=document.getElementById("refreshSessionsBtn");
const exportHistoryBtn=document.getElementById("exportHistoryBtn");
const exportHistoryCsvBtn=document.getElementById("exportHistoryCsvBtn");
const importHistoryBtn=document.getElementById("importHistoryBtn");
const importHistoryInput=document.getElementById("importHistoryInput");
const historyFiltersPanel=document.getElementById("historyFiltersPanel");
const historyStatusFilter=document.getElementById("historyStatusFilter");
const historyModeFilter=document.getElementById("historyModeFilter");
const historyNBackFilter=document.getElementById("historyNBackFilter");
const historyTrendFilter=document.getElementById("historyTrendFilter");
const historyCompletedSessions=document.getElementById("historyCompletedSessions");
const historyCorrectAnswers=document.getElementById("historyCorrectAnswers");
const historyDurationTrained=document.getElementById("historyDurationTrained");
const historyChartModeSelect=document.getElementById("historyChartModeSelect");
const historyChartNBackLevelSelect=document.getElementById("historyChartNBackLevelSelect");
const historyChartModeNote=document.getElementById("historyChartModeNote");
const accuracyTrendChart=document.getElementById("accuracyTrendChart");
const accuracyTrendDetails=document.getElementById("accuracyTrendDetails");
const responseTimeTrendChart=document.getElementById("responseTimeTrendChart");
const responseTimeTrendDetails=document.getElementById("responseTimeTrendDetails");
const latestIntervalChart=document.getElementById("latestIntervalChart");
const latestIntervalDetails=document.getElementById("latestIntervalDetails");
const latestIntervalBackBtn=document.getElementById("latestIntervalBackBtn");
const latestIntervalCaption=document.getElementById("latestIntervalCaption");
const recentSessionsList=document.getElementById("recentSessionsList");
const historyPaginationControls=document.querySelector(".history-pagination-controls");
const historyPaginationSummary=document.getElementById("historyPaginationSummary");
const historyPaginationIndicator=document.getElementById("historyPaginationIndicator");
const historyPrevPageBtn=document.getElementById("historyPrevPageBtn");
const historyNextPageBtn=document.getElementById("historyNextPageBtn");
const liveSettingsControls=[
  intervalIncrementSelect,
  durationInput,
  targetCorrectInput,
  correctThresholdInput,
  incorrectThresholdInput,
  playbackSpeedSelect,
  beepVolumeSelect
];
const committedSettingsControls=[
  endConditionSelect,
  modeSelect,
  nBackLevelInput,
  showAdvancedSettingsToggle,
  voiceSelect,
  beepToggle,
  themeToggle,
  showIntervalTimingToggle,
  hideTimerDuringSessionToggle
];

startBtn.onclick=startGame;
endSessionBtn.onclick=()=>stopGame("manual");
toggleSessionTimerBtn.onclick=()=>{
  if(sessionState!=="active" || endCondition!=="timer") return;
  applySessionTimerVisibility(!sessionTimerVisible);
  restoreAnswerFocus();
};
toggleSessionTimerBtn.addEventListener("pointerdown",event=>{
  if(sessionState!=="active") return;
  // Keep the answer field focused for mouse, touch, and pen activation.
  event.preventDefault();
  restoreAnswerFocus();
});
newSessionBtn.onclick=()=>setSessionState("idle");
resetSettingsBtn.onclick=resetSettingsToDefault;
themeToggle.onclick=()=>{
  const isDark=themeToggle.getAttribute("aria-pressed")==="true";
  themeToggle.setAttribute("aria-pressed",String(!isDark));
  handleSettingsChange({ currentTarget:themeToggle });
};
profileSelect.onchange=()=>{
  activateProfile(profileSelect.value);
};
newProfileBtn.onclick=()=>openProfileNameDialog("create");
renameProfileBtn.onclick=renameSelectedProfile;
deleteProfileBtn.onclick=deleteActiveProfile;
profileInfoBtn.onpointerenter=()=>{
  syncProfileInfoAria();
};
profileInfoBtn.onpointerleave=()=>{
  setTimeout(syncProfileInfoAria,0);
};
profileInfoBtn.onclick=event=>{
  event.stopPropagation();
  profileHelp.classList.toggle("tooltip-pinned");
  syncProfileInfoAria();
};
profileNameForm.addEventListener("submit",submitProfileNameDialog);
cancelProfileNameBtn.onclick=closeProfileNameDialog;
profileNameInput.addEventListener("input",()=>{
  profileNameError.textContent="";
  profileNameInput.removeAttribute("aria-invalid");
});
profileNameDialog.addEventListener("close",()=>{
  profileNameDialogAction=null;
  if(profileNameDialogTrigger instanceof HTMLElement){
    profileNameDialogTrigger.focus();
  }
  profileNameDialogTrigger=null;
});
confirmationForm.addEventListener("submit",submitConfirmationDialog);
cancelConfirmationBtn.onclick=closeConfirmationDialog;
confirmationDialog.addEventListener("close",()=>{
  confirmationDialogAction=null;
  if(confirmationDialogTrigger instanceof HTMLElement){
    confirmationDialogTrigger.focus();
  }
  confirmationDialogTrigger=null;
});
window.addEventListener("storage",event=>{
  if(event.key!==PROFILES_KEY || event.storageArea!==window.localStorage) return;
  if(settingsSaveTimerId!==null){
    clearTimeout(settingsSaveTimerId);
    settingsSaveTimerId=null;
  }
  const savedProfileState=readSavedProfiles();
  profiles=savedProfileState.profiles;
  activeProfileId=savedProfileState.activeProfileId || profiles[0]?.id || "";
  const activeProfile=findProfileById(activeProfileId);
  if(activeProfile) applySettings(activeProfile.settings);
  renderProfileOptions(activeProfileId);
  setProfileStatus("");
});
historyBtn.onclick=()=>{
  setHistoryVisible(true);
  void refreshHistoryView();
};
latestIntervalBackBtn.onclick=()=>{
  if(latestIntervalChartViewState.mode!=="detail") return;
  clearChartInteractions(latestIntervalChart);
  setLatestIntervalChartMode("overview",null);
  if(latestHistoryChartContext.latestTrace){
    renderLatestIntervalChart(latestHistoryChartContext.latestTrace);
  }
};
clearSessionsOnlyBtn.onclick=async()=>{
  openConfirmationDialog({
    title:"Clear Session Details",
    message:"Delete detailed session history? Lifetime totals and trend graphs will be preserved. This cannot be undone.",
    confirmLabel:"Clear Session Details",
    onConfirm:async()=>{
      try{
        await sessionHistoryStore.waitForWrites();
        setHistoryPageIndex(0);
        await sessionHistoryStore.clearSessionsOnly();
        await refreshHistoryView();
      }catch(e){
        setProfileStatus("This browser could not clear session details.","error");
      }
    }
  });
};
clearAllHistoryBtn.onclick=async()=>{
  openConfirmationDialog({
    title:"Clear All History",
    message:"Delete all saved history and totals from this browser? This cannot be undone.",
    confirmLabel:"Clear All History",
    onConfirm:async()=>{
      try{
        await sessionHistoryStore.waitForWrites();
        setHistoryPageIndex(0);
        await sessionHistoryStore.clearAll();
        await refreshHistoryView();
      }catch(e){
        setProfileStatus("This browser could not clear history.","error");
      }
    }
  });
};
historyFilterBtn.onclick=()=>{
  toggleHistoryFiltersVisible();
};
historyStatsHelp.onpointerenter=()=>{
  setHistoryStatsGlossaryVisible(true);
};
historyStatsHelp.onpointerleave=()=>{
  if(!historyStatsGlossaryPinned){
    setHistoryStatsGlossaryVisible(false);
  }
};
historyStatsHelp.onfocusin=()=>{
  if(historyStatsGlossaryEscapeDismissed){
    historyStatsGlossaryEscapeDismissed=false;
    return;
  }
  setHistoryStatsGlossaryVisible(true);
};
historyStatsHelp.onfocusout=()=>{
  setTimeout(()=>{
    if(!historyStatsGlossaryPinned && !historyStatsHelp.contains(document.activeElement)){
      setHistoryStatsGlossaryVisible(false);
    }
  },0);
};
historyStatsInfoBtn.onclick=event=>{
  event.stopPropagation();
  setHistoryStatsGlossaryPinned(!historyStatsGlossaryPinned);
  if(historyStatsGlossaryPinned || historyStatsHelp.matches(":hover") || historyStatsHelp.contains(document.activeElement)){
    setHistoryStatsGlossaryVisible(true);
  }else{
    setHistoryStatsGlossaryVisible(false);
  }
};
backFromHistoryBtn.onclick=()=>{
  closeHistoryStatsGlossary();
  setHistoryVisible(false);
};
refreshTrendChartsBtn.onclick=()=>{
  void refreshHistoryTrendCharts();
};
refreshSessionsBtn.onclick=()=>{
  void refreshHistorySessions();
};
exportHistoryBtn.onclick=async()=>{
  try{
    await sessionHistoryStore.waitForWrites();
    const data=await sessionHistoryStore.exportData();
    const blob=new Blob([JSON.stringify(data,null,2)],{ type:"application/json" });
    const url=URL.createObjectURL(blob);
    const link=document.createElement("a");
    link.href=url;
    link.download=`cct-data-backup-${formatExportFileDate()}.json`;
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  }catch(e){
    setProfileStatus("This browser could not export history.","error");
  }
};
exportHistoryCsvBtn.onclick=async()=>{
  try{
    const filtersSnapshot={ ...historyFilters };
    await sessionHistoryStore.waitForWrites();
    const sessions=applyHistoryFilters(await sessionHistoryStore.getAllSessions(),filtersSnapshot);
    const blob=new Blob(["\uFEFF",buildSessionHistoryCsv(sessions)],{ type:"text/csv;charset=utf-8" });
    const url=URL.createObjectURL(blob);
    const link=document.createElement("a");
    link.href=url;
    link.download=`cct-session-report-${formatExportFileDate()}.csv`;
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  }catch(e){
    setProfileStatus("This browser could not export the session report.","error");
  }
};
importHistoryBtn.onclick=()=>importHistoryInput.click();
importHistoryInput.onchange=async()=>{
  const file=importHistoryInput.files&&importHistoryInput.files[0];
  if(!file) return;
  try{
    await sessionHistoryStore.waitForWrites();
    const text=await file.text();
    const parsed=JSON.parse(text);
    await sessionHistoryStore.importData(parsed);
    setHistoryPageIndex(0);
    await refreshHistoryView();
  }catch(e){
    setProfileStatus("This browser could not import history.","error");
  }
  importHistoryInput.value="";
};
historyStatusFilter.onchange=()=>{
  setHistoryFilterValue("status",historyStatusFilter.value);
  void refreshHistorySessions();
};
historyModeFilter.onchange=()=>{
  setHistoryFilterValue("mode",historyModeFilter.value);
  void refreshHistorySessions();
};
historyNBackFilter.onchange=()=>{
  setHistoryFilterValue("nBackLevel",historyNBackFilter.value);
  void refreshHistorySessions();
};
historyTrendFilter.onchange=()=>{
  setHistoryFilterValue("trendInclusion",historyTrendFilter.value);
  void refreshHistorySessions();
};
historyChartModeSelect.onchange=()=>{
  setHistoryChartMode(historyChartModeSelect.value);
  void refreshHistoryTrendCharts();
};
historyChartNBackLevelSelect.onchange=()=>{
  setHistoryChartNBackLevel(historyChartNBackLevelSelect.value);
  void refreshHistoryTrendCharts();
};
resetHistoryFiltersBtn.onclick=()=>{
  resetHistoryFilters();
  void refreshHistorySessions();
};
historyPrevPageBtn.onclick=()=>{
  if(historyPageIndex<=0) return;
  setHistoryPageIndex(historyPageIndex-1);
  void refreshHistorySessions();
};
historyNextPageBtn.onclick=()=>{
  setHistoryPageIndex(historyPageIndex+1);
  void refreshHistorySessions();
};
voiceTestBtn.onclick=()=>{
  void testSelectedVoice();
};
beepTestBtn.onclick=()=>{
  playBeep(true);
};
normalThresholdPresetBtn.onclick=()=>applyThresholdPreset(4,4);
highAccuracyPresetBtn.onclick=()=>applyThresholdPreset(5,3);
thresholdInfoBtn.onpointerenter=()=>{
  syncThresholdInfoAria();
};
thresholdInfoBtn.onpointerleave=()=>{
  setTimeout(syncThresholdInfoAria,0);
};
thresholdInfoBtn.onclick=event=>{
  event.stopPropagation();
  thresholdHelp.classList.toggle("tooltip-pinned");
  syncThresholdInfoAria();
};
nBackInfoBtn.onpointerenter=()=>{
  syncNBackInfoAria();
};
nBackInfoBtn.onpointerleave=()=>{
  setTimeout(syncNBackInfoAria,0);
};
nBackInfoBtn.onclick=event=>{
  event.stopPropagation();
  nBackHelp.classList.toggle("tooltip-pinned");
  syncNBackInfoAria();
};
document.addEventListener("click",event=>{
  if(!thresholdHelp.contains(event.target)){
    thresholdHelp.classList.remove("tooltip-pinned");
    syncThresholdInfoAria();
  }
  if(!nBackHelp.contains(event.target)){
    nBackHelp.classList.remove("tooltip-pinned");
    syncNBackInfoAria();
  }
  if(!profileHelp.contains(event.target)){
    profileHelp.classList.remove("tooltip-pinned");
    syncProfileInfoAria();
  }
},true);
document.addEventListener("click",event=>{
  if(historyFilterVisible && historyFiltersPanel && historyFilterBtn && !historyFiltersPanel.contains(event.target) && !historyFilterBtn.contains(event.target)){
    toggleHistoryFiltersVisible(false);
  }
  if(historyStatsHelp && !historyStatsHelp.contains(event.target)){
    closeHistoryStatsGlossary();
  }
});
document.addEventListener("keydown",event=>{
  if(event.key!=="Escape") return;
  if(historyStatsGlossary && !historyStatsGlossary.classList.contains("hidden")){
    const infoButtonAlreadyFocused=document.activeElement===historyStatsInfoBtn;
    closeHistoryStatsGlossary();
    if(!infoButtonAlreadyFocused){
      historyStatsGlossaryEscapeDismissed=true;
      historyStatsInfoBtn.focus();
    }
  }
  if(thresholdHelp && (thresholdHelp.classList.contains("tooltip-pinned")
    || thresholdInfoBtn.matches(":hover"))){
    thresholdHelp.classList.remove("tooltip-pinned");
    syncThresholdInfoAria();
    thresholdInfoBtn.focus();
  }
  if(nBackHelp && (nBackHelp.classList.contains("tooltip-pinned")
    || nBackInfoBtn.matches(":hover"))){
    nBackHelp.classList.remove("tooltip-pinned");
    nBackInfoBtn.focus();
    syncNBackInfoAria();
  }
  if(profileHelp && (profileHelp.classList.contains("tooltip-pinned")
    || profileInfoBtn.matches(":hover"))){
    profileHelp.classList.remove("tooltip-pinned");
    profileInfoBtn.focus();
    syncProfileInfoAria();
  }
});
showAdvancedSettingsToggle.addEventListener("change",()=>{
  if(!showAdvancedSettingsToggle.checked){
    thresholdHelp.classList.remove("tooltip-pinned");
    nBackHelp.classList.remove("tooltip-pinned");
    syncThresholdInfoAria();
    syncNBackInfoAria();
  }
});
answer.addEventListener("input",checkInputLive);
document.addEventListener("pointerdown",event=>{
  if(sessionState!=="active") return;
  if(isAllowedSessionClick(event.target)) return;
  event.preventDefault();
  restoreAnswerFocus();
},true);
answer.addEventListener("blur",()=>{
  if(sessionState!=="active") return;
  setTimeout(()=>{
    if(sessionState==="active" && !isAllowedSessionClick(document.activeElement)){
      restoreAnswerFocus();
    }
  },0);
});
window.addEventListener("focus",()=>{
  if(sessionState==="active"){
    restoreAnswerFocus();
  }
});
document.addEventListener("visibilitychange",()=>{
  if(document.visibilityState==="visible" && sessionState==="active"){
    restoreAnswerFocus();
  }
});
liveSettingsControls.forEach(control=>{
  control.addEventListener("input",handleSettingsChange);
});
committedSettingsControls.forEach(control=>{
  control.addEventListener("change",handleSettingsChange);
});
[startingIntervalInput,maximumIntervalInput,minimumIntervalInput].forEach(input=>{
  input.addEventListener("change",()=>{
    validateIntervalInput(input);
  });
});
document.querySelectorAll(".interval-step-button").forEach(button=>{
  button.addEventListener("click",()=>{
    stepIntervalInput(button.dataset.intervalInput,button.dataset.intervalDirection);
  });
});
voiceSelect.addEventListener("focus",()=>{
  void refreshVoiceLibrary();
});
document.addEventListener("visibilitychange",()=>{
  if(document.visibilityState==="visible"){
    void refreshVoiceLibrary();
  }else if(settingsSaveTimerId!==null){
    saveSettings();
  }
});
window.addEventListener("pagehide",()=>{
  if(settingsSaveTimerId!==null){
    saveSettings();
  }
});
async function initializeApp(){
  await refreshVoiceLibrary();
  const savedProfileState=readSavedProfiles();
  profiles=savedProfileState.profiles;
  activeProfileId=savedProfileState.activeProfileId || profiles[0]?.id || "";
  if(!findProfileById(activeProfileId) && profiles[0]){
    activeProfileId=profiles[0].id;
  }
  const globalSettings=readSavedSettings();
  const activeSettings=findProfileById(activeProfileId)?.settings || globalSettings;
  applySettings({
    ...activeSettings,
    showAdvancedSettings:globalSettings.showAdvancedSettings,
    darkMode:globalSettings.darkMode
  });
  persistProfiles();
  persistSettings();
  renderProfileOptions(activeProfileId);
  setSessionState("idle");
  historyVisible=false;
  updateAppViews();
}

void initializeApp();
