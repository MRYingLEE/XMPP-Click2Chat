-- This is a role module for Prosody, created by Ying LI (Mr.Ying.LEE@Gmail.com)
-- All rights reserved. And related patent is pending.
-- The source code is forked from mod_muc of Prosody 0.9.9. And nearly all functions of MUC are kept but maybe in a different order, in a slightly changed name.

--[[  Basic idea:
-- 1. We try to make role is MUC compliant. At the front end, developer will treat Role as MUC.
-- 2. When non-member joins the template room, instead of rejection, we will create the non-member specific MUC. 
--    Later all coming stanza will be forwarded to the non-member specific MUC
-- 3. When a new stanza is sending to the non-member, we will translate a normal MUC stanza to the other specific MUC
-- In short, we use a gateway for non-member. The gateway is to transfer a non-member specific stanza to/from a template room's stanzas.
-- LY: So far, to simply, we only support template and instance on the same XMPP server
--]]

--[[ 
Routing function
1. Role MUC message is the basic and primary notification
2. The effect of invitiation is bad due to lack support at client side or bad (such as auto acceptance) support
3. The automatic status report is bad. 
4. Instead we should add Role specific command. such as "//L", "//l" as list.
5. To support smart routing, we will use assigned message format. So that a chatbot can work.
--]]


--[[ Source code protection and to make mainenance easy
  1. I use a wrapper to make receiveing and sending into few local function, so that the code of MUC is kept as much as possible.
  Later when a new version of MUC is released, we may upgrade ours easily
      module_send, origin_send
  
  2. To proect our source code,
    A. Combine source code in 1 file (done)
    B. Turn OOP to non_OOP
        Replace "\broom_mt:(\w+\s*)\(\)" with "room_mt__$1(SELF)"
        Replace "\broom_mt:(\w+\s*)\(" with "room_mt__$1(SELF,"
        \bself:\b(\w+)\(\) => room_mt__$1(SELF)
        \bself:\b(\w+)\( => room_mt__$1(SELF, 
        Replace "\bself\b" to "SELF" to avoid key word. !!! but some are room's internal functions, such as save, so replace selectively!!!
        to use \b(\w+\s*):(\w+\s*)\b to check missed conversion
        it is very easy to make mistakes 
    C. Mark every local function and members as local. (done)
    D. Short internal fields of room
    E. Mix with other Lua liberary by tools Squish
    F. Put some code in C liberary (Later)
    G. To use https://www.diffchecker.com/diff  check the modification
    
    3. All my own functions are started with "ly_", all modified heavily functions are ended with "_ly".
--]]

--[[ Roadmap
1. Salability. To protect privacy and security, we may genrate random template names at the beginning for clients. And the names have internal check method, such as CRC, so that a fake attack will be detected immediately without heavy cost.
2. Scalability. We may don't support public rooms. 
3. In the next version, we use  more OOP concept to organize code.(No! to improve efficiency and protct source code)
4. Statistics. For example, weekly, monthly visits of roles for management.
5. Security. Restrict MUC/Role Creating. Only a memeber of a role can generate a dynamic MUC in advance!!! 
6. Notification Settings: Reminding and/or Invitiation; timing: the 1st time, 1st message or at least 20 words. The event of join/left/disconnect reminding? 
7. Difference from a normal MUC. A lot of events will be save in history.
8. Improvement. To short specific MUC JID when the visitor comes from the same domain. To short the specific MUC JID for role actors. To make a MUC persistent if no actor response just in case info losing.
9. Maybe release a free edition, with limited functions, such as only first 2 actors are support, only same (local) domain are supported.
--]]

--[[  Lua coding hints
1. luac -l -l to check source code, use "/GETGLOBAL" to find some referenece mistakes
2. 

--]]
-- ********************** LY External Declare section
-- This is the only section to refer external modules and functions

local datetime = require "util.datetime";
local dataform = require "util.dataforms";

local jid_split = require "util.jid".split;
local jid_bare = require "util.jid".bare;
local jid_prep = require "util.jid".prep;

local st = require "util.stanza";
local log = require "util.logger".init("mod_role");  -- "mod_muc"); --changed by LY
local base64 = require "util.encodings".base64;
local md5 = require "util.hashes".md5;
--local muclib = module:require "role"; -- LY: changed from "muc"; And then disable this for the combining of files
--local jid_split = require "util.jid".split;  --LY: Disabled due to comibing of files
--local jid_bare = require "util.jid".bare; --LY: Disabled due to comibing of files
--local st = require "util.stanza"; --LY: Disabled due to comibing of files
local uuid_gen = require "util.uuid".generate;
local um_is_admin = require "core.usermanager".is_admin;
local hosts = prosody.hosts;
--local log = require "util.logger".init("mod_role");  -- Added by LY, just for debugging --LY: Disabled due to comibing of files

--local select = select;
local pairs, ipairs = pairs, ipairs;
local t_insert, t_remove = table.insert, table.remove;
local t_concat=table.concat; -- added by LY, to improve efficiency
local setmetatable = setmetatable;
local debug_traceback = debug.traceback;
local unpack, select = unpack, select;

-- ********************** LY "Global" Data structure section
-- These "Global" Data Structure are only visible to all functions o this module for they are locals.

-- Not needed local room_mt = { }; -- LY moved from back 
-- Not needed room_mt.__index = room_mt; -- LY moved from back

-- rooms = {};
-- local rooms = rooms;

local rooms = { }; -- LY: Combined the above 2 statements into 1 due to comibing of files -- Key data structure

local persistent_rooms_storage = module:open_store("persistent");
local persistent_rooms = persistent_rooms_storage:get() or {};  -- Key data structure
local room_configs = module:open_store("config");



local muc_domain = nil; -- module:get_host();
local default_history_length, max_history_length = 20, math.huge;

local SeperatorOfJID = "----"
local ReplaceStringOfAt = "--at--"

local muc_host = module:get_host();
local muc_name = module:get_option("name");
if type(muc_name) ~= "string" then muc_name = "Hotline.Chat Roles"; end
-- LY: muc_host is a special room also, but not in rooms
local host_room  --= muc_new_room(muc_host);
--host_room.route_stanza = room_route_stanza;  -- same as a common room
--host_room.save = room_save;  -- same as a common room

local restrict_room_creation = module:get_option("restrict_room_creation");
if restrict_room_creation then
  if restrict_room_creation == true then 
    restrict_room_creation = "admin";
  elseif restrict_room_creation ~= "admin" and restrict_room_creation ~= "local" then
    restrict_room_creation = nil;
  end
end

local valid_whois = {
  moderators = true,
  anyone = true,
}

local kickable_error_conditions = {
  ["gone"] = true;
  ["internal-server-error"] = true;
  ["item-not-found"] = true;
  ["jid-malformed"] = true;
  ["recipient-unavailable"] = true;
  ["redirect"] = true;
  ["remote-server-not-found"] = true;
  ["remote-server-timeout"] = true;
  ["service-unavailable"] = true;
  ["malformed error"] = true;
};

local saved = false;-- critical for module save

-- ********************** LY Function Declare section
-- this is section is to declare functions.
-- The reason we explicitly declare functions at the beginning is that to avoid function cross references with void result
--, which is a limit of Lua
local room_route_stanza
local room_save

local create_room
local get_disco_info
local get_disco_items

local handle_to_domain
local ly_isTemplateRoom
local ly_userRole2MUC
local ly_inherit
local ly_init_role_settings
local stanza_handler_ly
local shutdown_room
local shutdown_component
local is_admin
local ly_getInstanceRoomJID
local ly_getTemplateJIDAndOtherBareJID
local ly_MUC2UserRole
local ly_safeMUC2Role
local origin_send
local module_send
local ly_NotifyStatus
local ly_room_mt__IsOpen4Join
local ly_room_mt__NotifyTemplateRoomStatus
local ly_room_mt__NotifyTemplateRoom2Join_via_message
local room_mt__broadcast_except_nick_ly
local filter_xmlns_from_array
local filter_xmlns_from_stanza
local get_filtered_presence
local get_error_condition
local is_kickable_error
local getUsingPath
local getTag
local getText
local room_mt____tostring
local room_mt__get_default_role
local room_mt__broadcast_presence
local room_mt__broadcast_message
local room_mt__send_occupant_list
local room_mt__send_history
local room_mt__get_disco_info
local room_mt__get_disco_items
local room_mt__set_subject
local build_unavailable_presence_from_error
local room_mt__set_name
local room_mt__get_name
local room_mt__set_description_ly
local room_mt__get_description
local room_mt__set_password
local room_mt__get_password
local room_mt__set_moderated
local room_mt__is_moderated
local room_mt__set_members_only
local room_mt__is_members_only
local room_mt__set_persistent
local room_mt__is_persistent
local room_mt__set_hidden
local room_mt__is_hidden
local room_mt__set_changesubject
local room_mt__get_changesubject
local room_mt__get_historylength
local room_mt__set_historylength
local construct_stanza_id
local deconstruct_stanza_id
local room_mt__handle_to_occupant
local room_mt__send_form
local room_mt__get_form_layout
local room_mt__process_form
local room_mt__destroy
local room_mt__handle_to_room
local room_mt__handle_stanza
local room_mt__route_stanza
local room_mt__get_affiliation
local room_mt__set_affiliation
local room_mt__get_role
local room_mt__can_set_role
local room_mt__set_role
local room_mt___route_stanza
--local new_room
local set_max_history_length
local room_mt__getOccupantsCount
local room_mt__add_to_history
local room_mt__send_invitation
local room_mt__process_extended_description
local ly_xml2stanza
local Create_Persistent_Room
local InitModule

local muc_new_room  --=--[[muclib.  LY: Disabled due to combining--]] new_room;

-- **********************End of LY Function Declare section

-- **********************LY Function Define section (My own functions)

ly_getInstanceRoomJID=function(otherJID, templateRoomJID)
  --  local other_username, other_hostname, other_resource = jid_split(otherJID);
  --  local other_bare=jid_bare(otherJID)
  -- local template_username, template_hostname, template_resource = jid_split(templateRoomJID)
  -- local template_bare=jid_bare(templateRoomJID)
  local other_bare = jid_bare(otherJID)

  local instanceRoomJID = string.gsub(other_bare, "@", ReplaceStringOfAt) .. SeperatorOfJID .. templateRoomJID

  -- -- module:log("error", "otherJID= %s; templateRoomJID= %s; InstanceRoomJID=  %s", otherJID, templateRoomJID,instanceRoomJID);
  return instanceRoomJID;
end


ly_getTemplateJIDAndOtherBareJID=function(instanceRoomJID)
  -- local instance_username, instance_hostname, instance_resource = jid_split(instanceRoomJID)
  -- local instance_bare=jid_bare(instanceRoomJID)

  local i, j = string.find(instanceRoomJID, SeperatorOfJID, 1, true)

  -- -- module:log("error", "instance= %s; i= %s; j= %s",instanceRoomJID,tostring(i), tostring(j));

  if (i == nil) then
    return instanceRoomJID, ""
  end

  local tmpOther = string.sub(instanceRoomJID, 1, i - 1);
  local t1, t2 = string.find(tmpOther, ReplaceStringOfAt, 1, true);

  local otherBareJID

  if (t1 ~= nil) then
    otherBareJID = string.sub(tmpOther, 1, t1 - 1) .. "@" .. string.sub(tmpOther, t2 + 1)
  else
    otherBareJID = tmpOther
  end


  local templateJID = string.sub(instanceRoomJID, j + 1, #instanceRoomJID);

  -- -- module:log("error", "instance= %s; template= %s;tmpOther= %s; other= %s",instanceRoomJID, templateJID,tmpOther, otherBareJID);

  return templateJID, otherBareJID
end

-- When MUC sends a message from real MUC to the non-member
ly_MUC2UserRole=function(stanza)
  -- module:log("error", "**************original sending stanza: %s", tostring(stanza));

  local from_jid = stanza.attr.from
  local to_jid = stanza.attr.to

  --  local new_to_jid=to_jid


  --  local to_username, to_hostname, to_resource = jid_split(to_jid);
  local to_bare = jid_bare(to_jid)

  --  local from_username, from_hostname, from_resource = jid_split(from_jid)
  --  local from_bare=jid_bare(from_jid)

  local templateJID, otherBareJID = ly_getTemplateJIDAndOtherBareJID(from_jid);

  if (otherBareJID == to_bare) then
    local new_stanza = st.clone(stanza);
    -- LY: it s critical to clone one stanza for broadcast will share this stanza during a broadcast by changing the to only

    new_stanza.attr.from = templateJID

    -- module:log("error", "**************adjusted sending stanza: %s", tostring(new_stanza));

    return new_stanza;

  end
  -- module:log("error", "**************No Change in sending stanza");

  return stanza;

end


--[[
LY:
The only 2 functions to send Stanza out
1. We change call of origin.send(stanza) => origin_send(origin,stanza) to avoid too many changes
2. We change call of module:send(stanza) => module_send(stanza) to avoid too many changes
3. We modify stanza here, from instance room jid to template room jid when necessary
4. We will highly depend on XML operation on Stanza. We should be careful on different stanza.
--]]

ly_safeMUC2Role=function(stanza)
  local success, new_stanza = pcall(ly_MUC2UserRole, stanza);

  if success then
    return new_stanza
  else
    return stanza
  end
end

--[[
Routing
When the following things happened, the temp MUC will notify the template one:
The visitor sends the 1st message (This is the right time to remind members to join), just in case visitor doesn’t say anything. Later maybe improve.
The visitor leaves (This is the right time to remind to close the chat)
A member joins (This is the right time to remind other members)
A member leaves but the visitor is still in the MUC.
And every reminding, the system will list all not responding MUC in order for members to response.
I will check the logic of support chat
--]]

ly_NotifyStatus=function(instanceRoom, lastActivity)
  -- local templateRoom=getTemplateRoom(instanceRoom)
end

ly_room_mt__IsOpen4Join=function(SELF,templateJID)
  if room_mt__getOccupantsCount(SELF)==1 then
    return true
  else
    return false
  end
end

-- LY: to remind role members of the latest status of the template room
-- but the effect is not good. Too annoied to simple situcation, but too simple for complicated situation.
-- So maybe we will add a command such as "//l or //L", (actually "/l" or "L" due to escape). 
-- If someone send such a kind of message, system will reply a status for him.
ly_room_mt__NotifyTemplateRoomStatus=function(SELF,templateJID)
  local statistics = ""

  module:log("error", "SELF.jid= %s; templateJID= %s", tostring(SELF.jid),tostring(templateJID));

  local total, open, closed = 0, 0, 0

  for jid, room in pairs(rooms) do
    local localtemplateJID, otherBareJID = ly_getTemplateJIDAndOtherBareJID(jid);

    module:log("error", "localtemplateJID = %s, otherBareJID =%s", tostring(localtemplateJID),tostring(otherBareJID));

    if ((localtemplateJID == templateJID) and (otherBareJID~=""))then
      total = total + 1

      if (ly_room_mt__IsOpen4Join(room,templateJID)) then
        open = open + 1
        statistics = statistics .. room.jid .. "\n"
      end
    end
  end

  module:log("error", "1. statistics= %s", tostring(statistics));

  if (statistics ~= "") then
    local summary = "======Current Status=====\n Total:" .. tostring(total) .. ";"

    if (open > 0) then
      summary = summary .. "Open:" .. tostring(open) .. "as the following: \n"
    else
      summary = summary .. "\n"
    end

    module:log("error", "summary= %s", tostring(summary));
    return summary .. statistics
  else
    return ""
  end
end


-- LY: --  An improvement: To add reminding to message histroy so that reminding won't be missed.
-- LY: Another way to remind is to use invitation!
ly_room_mt__NotifyTemplateRoom2Join_via_message=function(SELF,stanza, current_bare_jid, also_invitiation)
  -- Added by LY
  -- Here, we need to check presence type and only process join notification.
  -- And later we should notification on all instance rooms.

  if (stanza.name == "presence") then
    -- module:log("error", "************** stanza attrr type =: %s", tostring(stanza.attr.type));
    if (not stanza.attr.type) then       -- online
      -- module:log("error", "**************presence stanza=: %s", tostring(stanza));
      -- module:log("error", "**************SELF.jid=: %s", tostring(SELF.jid));
      local templateJID, otherBareJID = ly_getTemplateJIDAndOtherBareJID(SELF.jid);

      -- module:log("error", "************** templateJID= %s, otherBareJID = %s", tostring( templateJID),tostring(otherBareJID));

      if (otherBareJID ~= "") then
        local templateRoom = rooms[templateJID]
        if (templateRoom ~= nil) then
          -- module:log("error", "**************templateRoom not nil, JID: %s", tostring(templateJID));

          local reminder = ""
          local reminder2="" -- to support simple client, who has no XMPP link support
--          local instances_status="" --discard for disabled status function

          local bare_from = jid_bare(stanza.attr.from)
          local aff = templateRoom._affiliations[current_bare_jid]

          -- module:log("error", "**************otherBareJID: %s; barefrom: %s", tostring(otherBareJID), bare_from);

          if ((aff == "none") or(aff == nil)) then
            -- other visits
            -- module:log("error", "**************others #(SELF._occupants)= %s",tostring(room_mt__getOccupantsCount(SELF)));
            if (room_mt__getOccupantsCount(SELF) <=1) then  -- no members in now
              reminder = "Please join: xmpp:" .. SELF.jid .. "?join to chat with " .. otherBareJID
              -- module:log("error", "**************please join reminder= %s; Occupants= %s", tostring(reminder), tostring(#(SELF._occupants)));
              reminder2=""  -- SELF.jid -- this is not helpful to solve the clickable link on Mobile phone

              --The invitiation effect is not good, so I discard this function
              if (also_invitiation) then
                for rnick, occupant in pairs(templateRoom._occupants) do
                  for jid in pairs(occupant.sessions) do
                    room_mt__send_invitation(SELF,bare_from,jid,"Dynamic invitiation by role of "..templateJID)
                  end
                end      
              end 
-- The status effect is bad. Too complicated for simple situation, but too simple for complicated situation
-- So I turn this as a user command
--              module:log("error", "ly_room_mt__NotifyTemplateRoomStatus jid= %s", tostring(SELF.jid));
--              instances_status=ly_room_mt__NotifyTemplateRoomStatus(SELF,templateJID);
            end
          else
            -- member joins
            if (room_mt__getOccupantsCount(SELF)>1) then -- in case as the 1st attendee, which is odd, maybe only in debugging
              reminder = current_bare_jid .. " has joined the chat of xmpp:" .. SELF.jid
              -- module:log("error", "**************joined reminder= %s", tostring(reminder));
--            module:log("error", "ly_room_mt__NotifyTemplateRoomStatus 2 jid= %s", tostring(SELF.jid));

--            instances_status=ly_room_mt__NotifyTemplateRoomStatus(SELF,templateJID);
            end
          end

          if (reminder ~= "") then
            local notification = st.message( { type = 'groupchat', from = templateJID }):tag('body'):text(reminder);

            room_mt__broadcast_message(templateRoom,notification, true)

            -- module:log("error", "**************notification: %s", tostring(notification));

            if (reminder2~="") then
              local notification2 = st.message( { type = 'groupchat', from = templateJID }):tag('body'):text(reminder2);

              room_mt__broadcast_message(templateRoom,notification2, true)

            end

--            if (instances_status~="") then
--              local notification3 = st.message( { type = 'groupchat', from = templateJID }):tag('body'):text(instances_status);

--              room_mt__broadcast_message(templateRoom,notification3, true)

--            end
            return
          end
        end       -- templateRoom~=nil
      end      -- otherBareJID~=""
    end     -- not presence.type
  end   -- (stanza.name=="presence")
  -- module:log("error", "**************No reminder needed");
  -- End of by LY
end




-- ************************** LY
-- A template must be persistent and public
-- Also template room is specific to assigned user. For memebers, the room is a normal one. for visitors, it is a template one.
-- Later we should enforce the requirement on template define.
ly_isTemplateRoom=function(room, from_user)
  -- module:log("error", "room.jid= %s; from_user=  %s", room.jid, from_user)

  local from_bare=jid_bare(from_user)

  local isTemplate=false;

  if (room==nil)  then
    -- module:log("error", "(room==nil)")

    return false;
  end

-- A template must be persistent and public
  if ((room._data.persistent==false) or (room._data.hidden)) then
    -- module:log("error", "(room._data.persistent==false) or (room._data.hidden)")
    return false
  end

-- just in case nested situation
  local templateJID, otherBareJID=ly_getTemplateJIDAndOtherBareJID(room.jid);

  if (otherBareJID==from_bare) then
    -- module:log("error", "templateJID=%s, otherBareJID== %s", templateJID, otherBareJID)
    return false
  end

-- if one is already a member of room, it is not template.
-- this is very important for member of a role. Or they cannot login to the role room
  if (room._affiliations==nil) then
    -- module:log("error", "room._affiliations==nil")
    return false;
  end;

  local affiliation=room._affiliations[from_bare]

  if (affiliation~=nil) then
    -- module:log("error", "affiliation= %s; from_bare=  %s", affiliation, from_bare)

    if (affiliation == "none") then
      isTemplate=true
      -- module:log("error", "affiliation == 'none'")
    end
  else
    isTemplate=true
    -- module:log("error", "affiliation == nil")
  end

  return isTemplate
end

--Added by LY: When MUC gets a message from non-member, we modify the message to fake its real from

ly_userRole2MUC=function(stanza)
  -- module:log("error", "**************Original Received stanza: %s", tostring(stanza));

  local from_jid=stanza.attr.from
  local to_jid=stanza.attr.to

  local new_to_jid=to_jid

  local to_username, to_hostname, to_resource = jid_split(to_jid);
  local to_bare=jid_bare(to_jid)

  local from_username, from_hostname = jid_split(from_jid)
  local from_bare=jid_bare(from_jid)

  local templateRoom=  rooms[to_bare] 

  -- -- module:log("error", "from %s to %s; from_username=  %s, from_hostname= %s; to_username= %s, to_hostname= %s, to_resouce= %s", from_jid, to_jid, from_username,from_hostname,to_username, to_hostname, to_resource) 

-- LY *******

  if ly_isTemplateRoom(templateRoom,from_jid) then
    -- Persistent but not in the member list, so it must be nonmember of template MUC
    new_to_jid=ly_getInstanceRoomJID(from_jid,to_jid)

    -- module:log("error", "**************from %s to %s", to_jid, new_to_jid);
    ---- module:log("error", "**************original Received stanza: %s", tostring(stanza));
    stanza.attr.to=new_to_jid;
    -- module:log("error", "**************adjusted Received stanza: %s", tostring(stanza));
  else
    -- module:log("error", "**************Not template, No Change Received stanza");
  end
end

-- Added by LY.
-- We copy settings of templateRoom to the instanceRoom.
-- The reason that I didn't add this as a method of a room class is that for unknown reason, the calling always failed
ly_inherit=function(instanceRoom,templateRoom)
  local needInherit=true

  if (templateRoom==nil) then
    -- module:log("error", "(templateRoom==nil)");
    needInherit=false
  end

  if (instanceRoom==templateRoom) then
    -- module:log("error", "(room==template)");
    needInherit=false
  end

  if needInherit then
    if (templateRoom._data==nil) then
      -- module:log("error", "(templateRoom._data==nil)");
      needInherit=false
    end
  end

  if (needInherit) then

    instanceRoom._data.description = templateRoom._data.description;

    instanceRoom._data['subject'] =templateRoom._data['subject'];

    --to disable for debugging
    if ((templateRoom._data.name~="") or (templateRoom._data.name~=nil)) then
      instanceRoom._data.name=templateRoom._data.name;
    else
      instanceRoom._data.name="Powered by Hotline.Chat. Keep typing, someone will repsonse you soon.";
    end

    --room._data.historylength(templateRoom._data.historylength);

    for jid, affiliation in pairs(templateRoom._affiliations) do
      instanceRoom._affiliations[jid]=affiliation
      -- module:log("error", "Template JID=  %s; affiliation= %s", tostring(jid), tostring(affiliation));  
    end
  end

  if #(instanceRoom._affiliations)~=#(templateRoom._affiliations) then
    -- module:log("error","#(room._affiliations)~=#(template._affiliations)");
  end
end

-- The reason that I didn't add this as a method of a room class is that for unknown reason, the calling always failed
ly_init_role_settings=function(instanceRoom)
  if (instanceRoom==nil) then
    -- module:log("error", "(room==nil)");
    return
  end

  if (instanceRoom._data==nil) then
    -- module:log("error", "(room._data==nil)");
    return
  end

  instanceRoom._data.whois='moderators' --'anyone'---

  instanceRoom._data.password=nil;

  instanceRoom._data.moderated=false;-- !!!!!!!!!! Don't set moderated to true. Due to unknown reasons, the whole function will fail if so.
  -- FIX here later.

  instanceRoom._data.members_only=true;-- for debug only, later we need to turn it off

  instanceRoom._data.hidden=false;-- for debug only, later we need to turn it off
  instanceRoom._data.changesubject=true;

  room_mt__set_persistent(instanceRoom,true);  -- instanceRoom._data.persistent=true; -- for debug only, later we need to leave it to users

end

-- LY: this function is modified from http://prosody.im/files/stanzaconv.lua
ly_xml2stanza= function(data)
-- Title:  Convert XML to Lua stanza generation code
-- Desc:   Takes XML as input and prints out the Lua code 
--         necessary to generate that XML.
-- Author: Matthew Wild <mwild1@gmail.com>
-- Date:   2009-04-05
-- URL:    http://prosody.im/files/stanzaconv.lua

--local data = io.read("*a");
  local stanza  --, table;

  local indent_char, indent_step = " ", 4;

  local indent, first, short_close = 0, true, nil;
  for tagline, text in data:gmatch("<([^>]+)>([^<]*)") do
    if tagline:sub(-1,-1) == "/" then
      tagline = tagline:sub(1, -2);
      short_close = true;
    end
    if tagline:sub(1,1) == "/" then
      --io.write(":up()");
      ---- module:log('error', 'create fakestanza :up()')
      stanza=stanza:up()

      indent = indent - indent_step;
    else
      local name, attr = tagline:match("^(%S*)%s*(.*)$");
      local attr_str = {};
      for k, _, v in attr:gmatch("(%S+)=([\"'])([^%2]-)%2") do
--        if #attr_str == 0 then
--          table.insert(attr_str, ", { ");
--        else
--          table.insert(attr_str, ", ");
--        end
        if k:match("^%a%w*$") then
          --  table.insert(attr_str, string.format("%s = %q", k, v));
          attr_str[k]=v;
        else
          --table.insert(attr_str, string.format("[%q] = %q", k, v));
          attr_str[k]=v;
        end
      end
--      if #attr_str > 0 then
--        table.insert(attr_str, " }");
--      end
      if first and name == "iq" or name == "presence" or name == "message" then
        -- io.write(string.format("stanza.%s(%s)", name, table.concat(attr_str):gsub("^, ", "")));
        ---- module:log('error', 'create fakestanza=%s', string.format("stanza.%s(%s)", name, table.concat(attr_str):gsub("^, ", "")))

        stanza=st.stanza(name,attr_str)

        first = nil;
      else
        -- io.write(string.format("\n%s:tag(%q%s)", indent_char:rep(indent), name, table.concat(attr_str)));
        if (name=="x") then
          -- module:log('error', 'create fakestanza tag=%s', tostring(attr_str))
        end

        stanza=stanza:tag(name, attr_str)

      end
      if not short_close then
        indent = indent + indent_step;
      end
    end
    if text and text:match("%S") then
      --io.write(string.format(":text(%q)", text));
      ---- module:log('error', 'create fakestanza text=%s', string.format(":text(%q)", text))

      stanza=stanza:text(text)

    elseif short_close then
      short_close = nil;
      --io.write(":up()");
      ---- module:log('error', 'create fakestanza :up()')

      stanza=stanza:up();
    end
  end

-- io.write("\n");

  ---- module:log('error', 'create fakestanza =%s', tostring(stanza))

  return stanza

end

--[[
-- LY: Digested and changed from function room_mt:process_form(origin, stanza)
-- Here, we don't inherit basic settings from template MUC. Instead we let client to decide how to create instance MUC.
-- But the afferikations are inherited from template MUC.
-- Later, we should let client to decide 
how to remind (via message or/and invitiation), 
the message template for noone in service, 
welcome message, 
chat restrictions: assigned list? local, logined, assigned hosts, blacklist?-- to copy that from chat 
In short, this is a business rule repository for this Role!
--]]
room_mt__process_extended_description=function(SELF)
--  local query = stanza.tags[1];
--  local form;
--  for _, tag in ipairs(query.tags) do if tag.name == "x" and tag.attr.xmlns == "jabber:x:data" then form = tag; break; end end
--  if not form then origin_send(origin, st.error_reply(stanza, "cancel", "service-unavailable")); return; end
--  if form.attr.type == "cancel" then origin_send(origin, st.reply(stanza)); return; end
--  if form.attr.type ~= "submit" then origin_send(origin, st.error_reply(stanza, "cancel", "bad-request", "Not a submitted form")); return; end
  local fake_stanza_str="<iq id='Hotline.Chat' type='set' to='yinglee@role.bizchat.us' from='yinglee@bizchat.us/Gajim'><query xmlns='http://jabber.org/protocol/muc#owner'>"..SELF._data.description.."</query></iq>"

  -- module:log('error', 'fakestanzastr=%s', tostring(fake_stanza_str))
  local success, fake_stanza=pcall(ly_xml2stanza,fake_stanza_str);

  if (not success) then -- to set default settings
    SELF.i.name=SELF._data.name
    SELF.i.description=""            --SELF._data.description
    SELF.i.persistent=false --SELF._data.persistent;
    SELF.i.moderated=true --SELF._data.moderated;
    SELF.i.membersonly=true --SELF._data.membersonly;
    SELF.i.hidden=true --SELF._data.hidden;
    SELF.i.changesubject=true --SELF._data.changesubject;
    SELF.i.historylength=SELF._data.historylength;
    SELF.i.whois='moderators' --SELF._data.whois
    SELF.i.password=nil --SELF._data.password

    -- module:log('error', 'bad extended description define=% s', tostring(fake_stanza_str))
    return
  end 

  -- module:log('error', 'fakestanza=%s', tostring(fake_stanza))

  local query = fake_stanza.tags[1];
  ---- module:log('error', 'query=%s', tostring(query))
  local form;
  for _, tag in ipairs(query.tags) do if tag.name == "x" and tag.attr.xmlns == "jabber:x:data" then form = tag; break; end end

  -- module:log('error', 'form=%s', tostring(form))

  local fields = room_mt__get_form_layout(SELF):data(form);

  -- module:log('error', 'fields=%s', tostring(fields))

  SELF.i.t=false; -- t: template

  if fields.FORM_TYPE ~= "http://jabber.org/protocol/muc#roomconfig" then 
    -- origin_send(origin, st.error_reply(stanza, "cancel", "bad-request", "Form is not of type room configuration")); 
    return; 
  end

  SELF.i.t=true; -- t: template
--  local dirty = false

--  local event = { room = SELF, fields = fields, changed = dirty };
--  module:fire_event("muc-config-submitted", event);
--  dirty = event.changed or dirty;

  local name = fields['muc#roomconfig_roomname'];
--  if name ~= room_mt__get_name(SELF) then
--    room_mt__set_name(SELF,name);
--  end
  SELF.i.name=name and SELF._data.name

  local description = fields['muc#roomconfig_roomdesc'];
--  if description ~= room_mt__get_description(SELF) then
--    room_mt__set_description_ly(SELF,description);
--  end
  SELF.i.name=description and SELF._data.description

  -- module:log("error", "extended_description description=%s", tostring(description));

  local persistent = fields['muc#roomconfig_persistentroom'];
--  dirty = dirty or(room_mt__is_persistent(SELF) ~= persistent)
--  -- module:log("error", "extended_description persistent=%s", tostring(persistent));
  SELF.i.persistent=persistent and SELF._data.persistent;


  local moderated = fields['muc#roomconfig_moderatedroom'];
--  dirty = dirty or(room_mt__is_moderated(SELF) ~= moderated)
--  -- module:log("error", "extended_description moderated=%s", tostring(moderated));
  SELF.i.moderated=moderated and SELF._data.moderated;

  local membersonly = fields['muc#roomconfig_membersonly'];
--  dirty = dirty or(room_mt__is_members_only(SELF) ~= membersonly)
--  -- module:log("error", "extended_description membersonly=%s", tostring(membersonly));
  SELF.i.membersonly=membersonly and SELF._data.membersonly;

  local public = fields['muc#roomconfig_publicroom'];
--  dirty = dirty or(room_mt__is_hidden(SELF) ~=(not public and true or nil))
  SELF.i.hidden=not public and SELF._data.hidden;

  local changesubject = fields['muc#roomconfig_changesubject'];
--  dirty = dirty or(room_mt__get_changesubject(SELF) ~=(not changesubject and true or nil))
  -- module:log('error', 'extended_description changesubject=%s', changesubject and "true" or "false")
  SELF.i.changesubject=changesubject and SELF._data.changesubject;

  local historylength = tonumber(fields['muc#roomconfig_historylength']);
--  dirty = dirty or(historylength and(room_mt__get_historylength(SELF) ~= historylength));
  -- module:log('error', 'extended_description historylength=%s', historylength)

  SELF.i.historylength=historylength and SELF._data.historylength;

  local whois = fields['muc#roomconfig_whois'];
  if not valid_whois[whois] then
--    origin_send(origin, st.error_reply(stanza, 'cancel', 'bad-request', "Invalid value for 'whois'"));
--    return;
    whois='moderators'
  end

  SELF.i.whois=whois and SELF._data.whois


--  local whois_changed = SELF._data.whois ~= whois
  -- SELF._data.whois = whois
  -- module:log('error', 'extended_description whois=%s', whois)

  local password = fields['muc#roomconfig_roomsecret'];

  SELF.i.password=password and SELF._data.password

  -- FIXME: we should set a suiatble settings according to the setting of the room (as template, or role MUC) 
  -- and also business logic: such as always member only without password to avoid confusion; always not public to others;

--  if room_mt__get_password(SELF) ~= password then
--    room_mt__set_password(SELF,password);
--  end

--  room_mt__set_moderated(SELF,moderated);
--  room_mt__set_members_only(SELF,membersonly);
--  room_mt__set_persistent(SELF,persistent);
--  room_mt__set_hidden(SELF,not public);
--  room_mt__set_changesubject(SELF,changesubject);
--  room_mt__set_historylength(SELF,historylength);

--  if SELF.save then SELF:save(true); end
--  origin_send(origin, st.reply(stanza));

--  if dirty or whois_changed then
--    local msg = st.message( { type = 'groupchat', from = SELF.jid })
--    :tag('x', { xmlns = 'http://jabber.org/protocol/muc#user' })

--    if dirty then
--      msg.tags[1]:tag('status', { code = '104' }):up();
--    end
--    if whois_changed then
--      local code =(whois == 'moderators') and "173" or "172";
--      msg.tags[1]:tag('status', { code = code }):up();
--    end

--    msg:up();

  --room_mt__broadcast_message(SELF,msg, false)
  -- module:log('error', 'SELF.i=%s', tostring(t_concat(SELF.i):gsub("^, ", "")))
end

-- **********************LY Critical Function Define section (Original or Slightly Modified from Prosody)

--**************** Room class define
--[[
We use more data structure driven code, in other words, memory for speed and code rubust such as
    Room._data
    {
    InstanceSerialNumber --Serial number for all instance of this template, used to short room name for members. We may recycle after some time, such as 1 day.

    GetASerialNumber();

    InstanceRooms(),
    NoOfInstanceRooms();
    HasMemeberIn(),  -- At least 1 memeber is inside
    Bool NotifiedTemplateAlready  -- the system at least notify the memebers of the role once or maybe after a while.

    templateRoom, -- to point to the template room, for instance room
    InstanceSerialNumber,
    Name4Other,   -- the name for other, at present, we use user JID+ Template JID for instance room
    Name4Memeber, -- the name for member of a role, at beginning we may use Template room name+SerialNumber() for instance room
    }


--]]
muc_new_room=function(jid, config)  -- renamed from new_room to short call chain
  return 
  --setmetatable(
  {
    jid = jid;
    _jid_nick = {};
    _occupants = {};
    _data = { -- LY: to short the name to d to protect source code
      whois = 'moderators';
      history_length = math.min((config and config.history_length)
        or default_history_length, max_history_length);
    };

    -- added by LY, i is for instance room settings, which is generated from description field.
    i= {
      whois = 'moderators';
      history_length = math.min((config and config.history_length)
        or default_history_length, max_history_length);
    };
    _affiliations = {};


    --LY: we should maintenance the link relations between template and instances carefully. So our code will be effient and robust
    --t=nil -- t for template room if this is an instance room. nil for template room.
    --s={} -- s for instance rooms if this is a template room. nil for instance room
  }
  --, room_mt)
  ;
end

room_save=function(room, forced) 
  local node = jid_split(room.jid);
  persistent_rooms[room.jid] = room._data.persistent;
  if room._data.persistent then
    local history = room._data.history;
    room._data.history = nil;
    local data = {
      jid = room.jid;
      _data = room._data;
      _affiliations = room._affiliations;
    };
    room_configs:set(node, data);
    room._data.history = history;
  elseif forced then
    room_configs:set(node, nil);
    if not next(room._occupants) then -- Room empty
      rooms[room.jid] = nil;
    end
  end
  if forced then persistent_rooms_storage:set(nil, persistent_rooms); end
end

create_room=function(jid)  
  -- LY: To avoid confusion, we don't change here. Instead we only turn templateRoom.JID=>instanceRoom.JID for non-members at the very beginning
  local room = muc_new_room(jid);
  --room.route_stanza = room_route_stanza; -- Later we should discard this field to improve efficiency and protect source code
  --room.save = room_save;             -- Later we should discard this field to improve efficiency and protect source code
  rooms[jid] = room;
  -- disabled module:fire_event("muc-room-created", { room = room }); -- Later we should discard all fire_event or changed to role specific event
  return room;
end

room_route_stanza=function(room, stanza) 
  module_send(stanza); 
end 

--****************End of Room class define

origin_send=function(origin, stanza)
  --- LY: Very careful, stanza is a common variable for a few sendings, so we have to clone it a new instance at first!
  origin.send(ly_safeMUC2Role(stanza))
end

module_send=function(stanza)
  module:send(ly_safeMUC2Role(stanza));
end

-- **********************LY Function Define section (Heavily Modified from Prosody)

-- LY: This function is the core to process received stanza
--Modified greatly here

stanza_handler_ly=function(event)
  local origin, stanza = event.origin, event.stanza;

  local original_to_barejid=jid_bare(stanza.attr.to)
  local original_from_barejid=jid_bare(stanza.attr.from)

  pcall(ly_userRole2MUC,stanza)

  local bare = jid_bare(stanza.attr.to);

  local room = rooms[bare];

  if not room then
    if stanza.name ~= "presence" then
      origin_send(origin,st.error_reply(stanza, "cancel", "item-not-found")); 
      return true;
    end
    if not(restrict_room_creation) or
    -- to_role or -- added by LY should enable later
    is_admin(stanza.attr.from) or
    (restrict_room_creation == "local" and select(2, jid_split(stanza.attr.from)) == module.host:gsub("^[^%.]+%.", "")) then
      room = create_room(bare);

      local instance=false

      --- LY we copy from template here, later we improve     
      local templateRoom=  rooms[original_to_barejid] 

      if ((room~=nil)) then
        -- module:log("error", "room=  %s; room.ly_inherit(templateRoom=%s )",bare, original_to_barejid);

        if (templateRoom==nil) then
          -- module:log("error", "(templateRoom==nil)");
        end

        if ((templateRoom~=nil) and (room~=templateRoom)) then  
          instance=true

          --LY: In such a situation, we may think this is a role instead of a normal meeting
          ly_init_role_settings(room);

          ly_inherit(room,templateRoom);

          if ((room._data['subject'] =="") or (room._data['subject'] ==nil)) then
            room._data['subject']="Powered by Hotline.Chat"
            -- module:log("error", "SELF._data['subject']=  %s", tostring(room._data['subject']));  
          end
        end
      end

      local affiliation= room_mt__get_affiliation(room,original_from_barejid)

      if affiliation==nil then
        if instance then
          room._affiliations[original_from_barejid]="member"
        else
          room._affiliations[original_from_barejid]="owner"
        end

        -- module:log("error", "%s= member", original_from_barejid);
      end

      for jid, affiliation in pairs(room._affiliations) do
        -- module:log("error", "JID=  %s; affiliation= %s", tostring(jid), tostring(affiliation));  
      end
    end
  end
--- My modification in this function is ended here

  if room then
    room_mt__handle_stanza(room,origin, stanza);
    if not next(room._occupants) and not persistent_rooms[room.jid] then -- empty, non-persistent room
      -- disabled module:fire_event("muc-room-destroyed", { room = room });
      rooms[bare] = nil; -- discard room
    end
  else
    origin_send(origin,st.error_reply(stanza, "cancel", "not-allowed"));  
  end
  return true;
end
--LY: the event hook to process received message

room_mt__broadcast_except_nick_ly=function(SELF,stanza, nick)
  -- Modified by LY in this function
  local current_occupant = nil;  -- added by LY

  for rnick, occupant in pairs(SELF._occupants) do
    if rnick ~= nick then
      for jid in pairs(occupant.sessions) do
        stanza.attr.to = jid;
        room_mt___route_stanza(SELF,stanza);
      end
    else       -- added by LY
      current_occupant = occupant       -- added by LY
    end     -- added by LY
  end

  local current_bare_jid = jid_bare(current_occupant.jid);   -- added by LY
  ---- module:log("error", "**************current_bare_jid=: %s", tostring(current_bare_jid));

-- To my surprise, the invitiation function is not well implemented in client side
-- At the same time, some client automatically accepts invitiation, which causes confusion.
-- Even so, for there is no good clickable URI support on Mobile. I STILL use inviatition until the ability is ready!!!
-- Of course, later, it is clients to decide to use invitiation and/or URI reminding
  local via_invitiation=true

  ly_room_mt__NotifyTemplateRoom2Join_via_message(SELF,stanza, current_bare_jid,via_invitiation)   -- added by LY

end


room_mt__set_description_ly=function(SELF,description)
  if description == "" or type(description) ~= "string" then description = nil; end
  if SELF._data.description ~= description then
    SELF._data.description = description;

    -- module:log('error', 'extended_description=%s', description)
    pcall(room_mt__process_extended_description,SELF) -- added by LY

    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

-- **********************LY Function Define section (Original or Slightly Modified from Prosody)

local pcall = function(f, ...)
  --- digested from other lua lib of Prosody
  -- this function is an easy way to deal with exceptions
  local n = select("#", ...);
  local params = { ...};
  return xpcall( function() return f(unpack(params, 1, n)) end, function(e) return tostring(e) .. "\n" .. debug_traceback(); end);
end

is_admin=function(jid)  -- LY moved from back 
  return um_is_admin(jid, module.host);
end
--[[-- LY********
      local to_username, to_hostname = jid_split(stanza.attr.to);
      local to_bare=jid_bare(stanza.attr.to)

      local from_username, from_hostname, from_resource = jid_split(stanza.attr.from)
      -- local from_bare=jid_bare(stanza.attr.from)

      if occupant.affiliation ~= "owner" and occupant.affiliation ~= "admin" then
        -- we may think its non-member of template MUC.
        local i, j = string.find(from_username,SeperatorOfJID+to_username)

        if j==#from_username then
          if from_resource then
            stanza.attrr.from=string.sub(from_username,1,i-1)+"@"+from_hostname+"/"+from_resource
          else
            stanza.attrr.from=string.sub(from_username,1,i-1)+"@"+from_hostname
          end

        end -- we change from here
      end

--]]


filter_xmlns_from_array=function(array, filters)
  local count = 0;
  for i = #array, 1, -1 do
    local attr = array[i].attr;
    if filters[attr and attr.xmlns] then
      t_remove(array, i);
      count = count + 1;
    end
  end
  return count;
end

filter_xmlns_from_stanza=function(stanza, filters)
  if filters then
    if filter_xmlns_from_array(stanza.tags, filters) ~= 0 then
      return stanza, filter_xmlns_from_array(stanza, filters);
    end
  end
  return stanza, 0;
end
local presence_filters = { ["http://jabber.org/protocol/muc"] = true;["http://jabber.org/protocol/muc#user"] = true };

get_filtered_presence=function(stanza)
  return filter_xmlns_from_stanza(st.clone(stanza):reset(), presence_filters);
end

get_error_condition=function(stanza)
  local _, condition = stanza:get_error();
  return condition or "malformed error";
end

is_kickable_error=function(stanza)
  local cond = get_error_condition(stanza);
  return kickable_error_conditions[cond] and cond;
end

getUsingPath=function(stanza, path, getText)
  local tag = stanza;
  for _, name in ipairs(path) do
    if type(tag) ~= 'table' then return; end
    tag = tag:child_with_name(name);
  end
  if tag and getText then tag =t_concat(tag); end
  return tag;
end


getTag=function(stanza, path) return getUsingPath(stanza, path); end
getText=function(stanza, path) return getUsingPath(stanza, path, true); end

room_mt____tostring=function(SELF)
  return "MUC room (" .. SELF.jid .. ")";
end


room_mt__get_default_role=function(SELF,affiliation)
  if affiliation == "owner" or affiliation == "admin" then
    return "moderator";
  elseif affiliation == "member" then
    return "participant";
  elseif not affiliation then
    if not room_mt__is_members_only(SELF) then
      return room_mt__is_moderated(SELF) and "visitor" or "participant";
    end
  end
end


room_mt__broadcast_presence=function(SELF,stanza, sid, code, nick)
  stanza = get_filtered_presence(stanza);
  local occupant = SELF._occupants[stanza.attr.from];
  stanza:tag("x", { xmlns = 'http://jabber.org/protocol/muc#user' })
  :tag("item", { affiliation = occupant.affiliation or "none", role = occupant.role or "none", nick = nick }):up();
  if code then
    stanza:tag("status", { code = code }):up();
  end
  room_mt__broadcast_except_nick_ly(SELF,stanza, stanza.attr.from);

  local me = SELF._occupants[stanza.attr.from];
  if me then
    stanza:tag("status", { code = '110' }):up();
    stanza.attr.to = sid;

    ---- module:log("error", "self jid=%s; conferm Stanza= %s;",tostring(SELF.jid),tostring(stanza)); -- Added by LY, for debug
    room_mt___route_stanza(SELF,stanza);
  else
    ---- module:log("error", "Not found in SELF._occupants SELF.jid= %s; from= %s;",tostring(SELF.jid),tostring(stanza.attr.from)); -- Added by LY, for debug
  end
end

--LY: Digested from room_mt__broadcast_message=function(SELF,stanza, historic)
room_mt__add_to_history=function (SELF, stanza)

-- add to history
  local history = SELF._data['history'];
  if not history then history = { }; SELF._data['history'] = history; end
  stanza = st.clone(stanza);
  stanza.attr.to = "";
  local stamp = datetime.datetime();
  stanza:tag("delay", { xmlns = "urn:xmpp:delay", from = muc_domain, stamp = stamp }):up();
-- XEP-0203
  stanza:tag("x", { xmlns = "jabber:x:delay", from = muc_domain, stamp = datetime.legacy() }):up();
-- XEP-0091 (deprecated)
  local entry = { stanza = stanza, stamp = stamp };
  t_insert(history, entry);
  while #history >(SELF._data.history_length or default_history_length) do t_remove(history, 1) end
end

room_mt__broadcast_message=function(SELF,stanza, historic)
  -- LY: NOT the only way to send !
  -- -- module:log("error", "**************broadcast_message: %s", tostring(stanza));

  local to = stanza.attr.to;
  for occupant, o_data in pairs(SELF._occupants) do
    for jid in pairs(o_data.sessions) do
      stanza.attr.to = jid;
      room_mt___route_stanza(SELF,stanza);
    end
  end
  stanza.attr.to = to;
  if historic then
    room_mt__add_to_history(SELF, stanza)
  end
end

room_mt__send_occupant_list=function(SELF,to)
  -- LY: We should check this function later in case we need translate item also
  local current_nick = SELF._jid_nick[to];
  for occupant, o_data in pairs(SELF._occupants) do
    if occupant ~= current_nick then
      local pres = get_filtered_presence(o_data.sessions[o_data.jid]);
      pres.attr.to, pres.attr.from = to, occupant;
      pres:tag("x", { xmlns = 'http://jabber.org/protocol/muc#user' })
      :tag("item", { affiliation = o_data.affiliation or "none", role = o_data.role or "none" }):up();
      room_mt___route_stanza(SELF,pres);
    end
  end
end

room_mt__send_history=function(SELF,to, stanza)
  -- LY: we should not send histroy to non-member of template room just in case privacy
  local history = SELF._data['history'];
  -- send discussion history
  if history then
    local x_tag = stanza and stanza:get_child("x", "http://jabber.org/protocol/muc");
    local history_tag = x_tag and x_tag:get_child("history", "http://jabber.org/protocol/muc");

    local maxchars = history_tag and tonumber(history_tag.attr.maxchars);
    if maxchars then maxchars = math.floor(maxchars); end

    local maxstanzas = math.floor(history_tag and tonumber(history_tag.attr.maxstanzas) or #history);
    if not history_tag then maxstanzas = 20; end

    local seconds = history_tag and tonumber(history_tag.attr.seconds);
    if seconds then seconds = datetime.datetime(os.time() - math.floor(seconds)); end

    local since = history_tag and history_tag.attr.since;
    if since then since = datetime.parse(since); since = since and datetime.datetime(since); end
    if seconds and(not since or since < seconds) then since = seconds; end

    local n = 0;
    local charcount = 0;

    for i = #history, 1, -1 do
      local entry = history[i];
      if maxchars then
        if not entry.chars then
          entry.stanza.attr.to = "";
          entry.chars = #tostring(entry.stanza);
        end
        charcount = charcount + entry.chars + #to;
        if charcount > maxchars then break; end
      end
      if since and since > entry.stamp then break; end
      if n + 1 > maxstanzas then break; end
      n = n + 1;
    end
    for i = #history - n + 1, #history do
      local msg = history[i].stanza;
      msg.attr.to = to;
      room_mt___route_stanza(SELF,msg);
    end
  end
  if SELF._data['subject'] then
    room_mt___route_stanza(SELF,st.message( { type = 'groupchat', from = SELF._data['subject_from'] or SELF.jid, to = to }):tag("subject"):text(SELF._data['subject']));
  end
end

-- LY: Digested from room_mt__get_disco_info=function(SELF,stanza)
room_mt__getOccupantsCount=function(SELF)
  local count = 0;
  for _ in pairs(SELF._occupants) do count = count + 1; end
  return count
end

room_mt__get_disco_info=function(SELF,stanza)
  local count = 0;
  for _ in pairs(SELF._occupants) do count = count + 1; end
  return st.reply(stanza):query("http://jabber.org/protocol/disco#info")
  :tag("identity", { category = "conference", type = "text", name = room_mt__get_name(SELF) }):up()
  :tag("feature", { var = "http://jabber.org/protocol/muc" }):up()
  :tag("feature", { var = room_mt__get_password(SELF) and "muc_passwordprotected" or "muc_unsecured" }):up()
  :tag("feature", { var = room_mt__is_moderated(SELF) and "muc_moderated" or "muc_unmoderated" }):up()
  :tag("feature", { var = room_mt__is_members_only(SELF) and "muc_membersonly" or "muc_open" }):up()
  :tag("feature", { var = room_mt__is_persistent(SELF) and "muc_persistent" or "muc_temporary" }):up()
  :tag("feature", { var = room_mt__is_hidden(SELF) and "muc_hidden" or "muc_public" }):up()
  :tag("feature", { var = SELF._data.whois ~= "anyone" and "muc_semianonymous" or "muc_nonanonymous" }):up()
  :add_child(dataform.new( {
        { name = "FORM_TYPE", type = "hidden", value = "http://jabber.org/protocol/muc#roominfo" },
        { name = "muc#roominfo_description", label = "Description", value = "" },
        { name = "muc#roominfo_occupants", label = "Number of occupants", value = tostring(count) }
        } ):form( { ["muc#roominfo_description"] = room_mt__get_description(SELF) }, 'result'))
  ;
end

room_mt__get_disco_items=function(SELF,stanza)
  local reply = st.reply(stanza):query("http://jabber.org/protocol/disco#items");
  for room_jid in pairs(SELF._occupants) do
    reply:tag("item", { jid = room_jid, name = room_jid:match("/(.*)") }):up();
  end
  return reply;
end

room_mt__set_subject=function(SELF,current_nick, subject)
  -- TODO check nick's authority
  if subject == "" then subject = nil; end
  SELF._data['subject'] = subject;
  SELF._data['subject_from'] = current_nick;
  room_save(SELF) --if SELF.save then SELF:save(); end
  local msg = st.message( { type = 'groupchat', from = current_nick })
  :tag('subject'):text(subject):up();
  room_mt__broadcast_message(SELF,msg, false);
  return true;
end


build_unavailable_presence_from_error=function(stanza)
  local type, condition, text = stanza:get_error();
  local error_message = "Kicked: " ..(condition and condition:gsub("%-", " ") or "presence error");
  if text then
    error_message = error_message .. ": " .. text;
  end
  return st.presence( { type = 'unavailable', from = stanza.attr.from, to = stanza.attr.to })
  :tag('status'):text(error_message);
end


room_mt__set_name=function(SELF,name)
  if name == "" or type(name) ~= "string" or name ==(jid_split(SELF.jid)) then name = nil; end
  if SELF._data.name ~= name then
    SELF._data.name = name;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__get_name=function(SELF)
  return SELF._data.name or jid_split(SELF.jid);
end


room_mt__get_description=function(SELF)
  return SELF._data.description;
end

room_mt__set_password=function(SELF,password)
  if password == "" or type(password) ~= "string" then password = nil; end
  if SELF._data.password ~= password then
    SELF._data.password = password;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__get_password=function(SELF)
  return SELF._data.password;
end

room_mt__set_moderated=function(SELF,moderated)
  moderated = moderated and true or nil;
  if SELF._data.moderated ~= moderated then
    SELF._data.moderated = moderated;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__is_moderated=function(SELF)
  return SELF._data.moderated;
end

room_mt__set_members_only=function(SELF,members_only)
  members_only = members_only and true or nil;
  if SELF._data.members_only ~= members_only then
    SELF._data.members_only = members_only;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__is_members_only=function(SELF)
  return SELF._data.members_only;
end

room_mt__set_persistent=function(SELF,persistent)
  persistent = persistent and true or nil;
  if SELF._data.persistent ~= persistent then
    SELF._data.persistent = persistent;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__is_persistent=function(SELF)
  return SELF._data.persistent;
end

room_mt__set_hidden=function(SELF,hidden)
  hidden = hidden and true or nil;
  if SELF._data.hidden ~= hidden then
    SELF._data.hidden = hidden;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__is_hidden=function(SELF)
  return SELF._data.hidden;
end

room_mt__set_changesubject=function(SELF,changesubject)
  changesubject = changesubject and true or nil;
  if SELF._data.changesubject ~= changesubject then
    SELF._data.changesubject = changesubject;
    room_save(SELF,true) --if SELF.save then SELF:save(true); end
  end
end

room_mt__get_changesubject=function(SELF)
  return SELF._data.changesubject;
end

room_mt__get_historylength=function(SELF)
  return SELF._data.history_length or default_history_length;
end

room_mt__set_historylength=function(SELF,length)
  length = math.min(tonumber(length) or default_history_length, max_history_length or math.huge);
  if length == default_history_length then
    length = nil;
  end
  SELF._data.history_length = length;
end



construct_stanza_id=function(room, stanza)
  local from_jid, to_nick = stanza.attr.from, stanza.attr.to;
  local from_nick = room._jid_nick[from_jid];
  local occupant = room._occupants[to_nick];
  local to_jid = occupant.jid;

  return from_nick, to_jid, base64.encode(to_jid .. "\0" .. stanza.attr.id .. "\0" .. md5(from_jid));
end

deconstruct_stanza_id=function(room, stanza)
  local from_jid_possiblybare, to_nick = stanza.attr.from, stanza.attr.to;
  local from_jid, id, to_jid_hash =(base64.decode(stanza.attr.id) or ""):match("^(%Z+)%z(%Z*)%z(.+)$");
  local from_nick = room._jid_nick[from_jid];

  if not(from_nick) then return; end
  if not(from_jid_possiblybare == from_jid or from_jid_possiblybare == jid_bare(from_jid)) then return; end

  local occupant = room._occupants[to_nick];
  for to_jid in pairs(occupant and occupant.sessions or { }) do
    if md5(to_jid) == to_jid_hash then
      return from_nick, to_jid, id;
    end
  end
end



room_mt__handle_to_occupant=function(SELF,origin, stanza)
  -- PM, vCards, etc
  -- LY: So far private message is not intended to be supported! I need check later!!!
  local from, to = stanza.attr.from, stanza.attr.to;
  local room = jid_bare(to);
  local current_nick = SELF._jid_nick[from];
  local type = stanza.attr.type;
  log("debug", "room: %s, current_nick: %s, stanza: %s", room or "nil", current_nick or "nil", stanza:top_tag());
  if (select(2, jid_split(from)) == muc_domain) then error("Presence from the MUC itself!!!"); end
  if stanza.name == "presence" then
    local pr = get_filtered_presence(stanza);
    pr.attr.from = current_nick;
    if type == "error" then
      -- error, kick em out!
      if current_nick then
        log("debug", "kicking %s from %s", current_nick, room);
        room_mt__handle_to_occupant(SELF,origin, build_unavailable_presence_from_error(stanza));
      end
    elseif type == "unavailable" then
      -- unavailable
      if current_nick then
        log("debug", "%s leaving %s", current_nick, room);
        SELF._jid_nick[from] = nil;
        local occupant = SELF._occupants[current_nick];
        local new_jid = next(occupant.sessions);
        if new_jid == from then new_jid = next(occupant.sessions, new_jid); end
        if new_jid then
          local jid = occupant.jid;
          occupant.jid = new_jid;
          occupant.sessions[from] = nil;
          pr.attr.to = from;
          pr:tag("x", { xmlns = 'http://jabber.org/protocol/muc#user' })
          :tag("item", { affiliation = occupant.affiliation or "none", role = 'none' }):up()
          :tag("status", { code = '110' }):up();
          room_mt___route_stanza(SELF,pr);
          if jid ~= new_jid then
            pr = st.clone(occupant.sessions[new_jid])
            :tag("x", { xmlns = 'http://jabber.org/protocol/muc#user' })
            :tag("item", { affiliation = occupant.affiliation or "none", role = occupant.role or "none" });
            pr.attr.from = current_nick;
            room_mt__broadcast_except_nick_ly(SELF,pr, current_nick);
          end
        else
          occupant.role = 'none';
          room_mt__broadcast_presence(SELF,pr, from);
          SELF._occupants[current_nick] = nil;
        end
      end
    elseif not type then
      -- available
      if current_nick then
        -- if #pr == #stanza or current_nick ~= to then -- commented because google keeps resending directed presence
        if current_nick == to then
          -- simple presence
          log("debug", "%s broadcasted presence", current_nick);
          SELF._occupants[current_nick].sessions[from] = pr;
          room_mt__broadcast_presence(SELF,pr, from);
        else
          -- change nick
          local occupant = SELF._occupants[current_nick];
          local is_multisession = next(occupant.sessions, next(occupant.sessions));
          if SELF._occupants[to] or is_multisession then
            log("debug", "%s couldn't change nick", current_nick);
            local reply = st.error_reply(stanza, "cancel", "conflict"):up();
            reply.tags[1].attr.code = "409";
            origin_send(origin, reply:tag("x", { xmlns = "http://jabber.org/protocol/muc" }));
          else
            local data = SELF._occupants[current_nick];
            local to_nick = select(3, jid_split(to));
            if to_nick then
              log("debug", "%s (%s) changing nick to %s", current_nick, data.jid, to);
              local p = st.presence( { type = 'unavailable', from = current_nick });
              room_mt__broadcast_presence(SELF,p, from, '303', to_nick);
              SELF._occupants[current_nick] = nil;
              SELF._occupants[to] = data;
              SELF._jid_nick[from] = to;
              pr.attr.from = to;
              SELF._occupants[to].sessions[from] = pr;
              room_mt__broadcast_presence(SELF,pr, from);
            else
              -- TODO malformed-jid
            end
          end
        end
        -- else -- possible rejoin
        -- log("debug", "%s had connection replaced", current_nick);
        -- room_mt__handle_to_occupant(SELF,origin, st.presence({type='unavailable', from=from, to=to})
        -- 	:tag('status'):text('Replaced by new connection'):up()); -- send unavailable
        -- room_mt__handle_to_occupant(SELF,origin, stanza); -- resend available
        -- end
      else
        -- enter room
        local new_nick = to;
        local is_merge;
        if SELF._occupants[to] then
          if jid_bare(from) ~= jid_bare(SELF._occupants[to].jid) then
            new_nick = nil;
          end
          is_merge = true;
        end
        local password = stanza:get_child("x", "http://jabber.org/protocol/muc");
        password = password and password:get_child("password", "http://jabber.org/protocol/muc");
        password = password and password[1] ~= "" and password[1];
        if room_mt__get_password(SELF) and room_mt__get_password(SELF) ~= password then
          log("debug", "%s couldn't join due to invalid password: %s", from, to);
          local reply = st.error_reply(stanza, "auth", "not-authorized"):up();
          reply.tags[1].attr.code = "401";
          origin_send(origin, reply:tag("x", { xmlns = "http://jabber.org/protocol/muc" }));
        elseif not new_nick then
          log("debug", "%s couldn't join due to nick conflict: %s", from, to);
          local reply = st.error_reply(stanza, "cancel", "conflict"):up();
          reply.tags[1].attr.code = "409";
          origin_send(origin, reply:tag("x", { xmlns = "http://jabber.org/protocol/muc" }));
        else
          log("debug", "%s joining as %s", from, to);
          if not next(SELF._affiliations) then
            -- new room, no owners
            SELF._affiliations[jid_bare(from)] = "owner";
          end
          local affiliation = room_mt__get_affiliation(SELF,from);
          local role = room_mt__get_default_role(SELF,affiliation)
          if role then
            -- new occupant
            if not is_merge then
              SELF._occupants[to] = { affiliation = affiliation, role = role, jid = from, sessions = { [from] = get_filtered_presence(stanza) } };
            else
              SELF._occupants[to].sessions[from] = get_filtered_presence(stanza);
            end
            SELF._jid_nick[from] = to;
            room_mt__send_occupant_list(SELF,from);
            pr.attr.from = to;
            pr:tag("x", { xmlns = 'http://jabber.org/protocol/muc#user' })
            :tag("item", { affiliation = affiliation or "none", role = role or "none" }):up();
            if not is_merge then
              room_mt__broadcast_except_nick_ly(SELF,pr, to);
            end
            pr:tag("status", { code = '110' }):up();
            if SELF._data.whois == 'anyone' then
              pr:tag("status", { code = '100' }):up();
            end
            pr.attr.to = from;
            room_mt___route_stanza(SELF,pr);
            room_mt__send_history(SELF,from, stanza);
          elseif not affiliation then
            -- registration required for entering members-only room
            local reply = st.error_reply(stanza, "auth", "registration-required"):up();
            reply.tags[1].attr.code = "407";
            origin_send(origin, reply:tag("x", { xmlns = "http://jabber.org/protocol/muc" }));
          else
            -- banned
            local reply = st.error_reply(stanza, "auth", "forbidden"):up();
            reply.tags[1].attr.code = "403";
            origin_send(origin, reply:tag("x", { xmlns = "http://jabber.org/protocol/muc" }));
          end
        end
      end
    elseif type ~= 'result' then
      -- bad type
      if type ~= 'visible' and type ~= 'invisible' then
        -- COMPAT ejabberd can broadcast or forward XEP-0018 presences
        origin_send(origin, st.error_reply(stanza, "modify", "bad-request"));
        -- FIXME correct error?
      end
    end
  elseif not current_nick then
    -- not in room
    if (type == "error" or type == "result") and stanza.name == "iq" then
      local id = stanza.attr.id;
      stanza.attr.from, stanza.attr.to, stanza.attr.id = deconstruct_stanza_id(SELF, stanza);
      if stanza.attr.id then
        room_mt___route_stanza(SELF,stanza);
      end
      stanza.attr.from, stanza.attr.to, stanza.attr.id = from, to, id;
    elseif type ~= "error" then
      origin_send(origin, st.error_reply(stanza, "cancel", "not-acceptable"));
    end
  elseif stanza.name == "message" and type == "groupchat" then
    -- groupchat messages not allowed in PM
    origin_send(origin, st.error_reply(stanza, "modify", "bad-request"));
  elseif current_nick and stanza.name == "message" and type == "error" and is_kickable_error(stanza) then
    log("debug", "%s kicked from %s for sending an error message", current_nick, SELF.jid);
    room_mt__handle_to_occupant(SELF,origin, build_unavailable_presence_from_error(stanza));
    -- send unavailable
  else
    -- private stanza
    local o_data = SELF._occupants[to];
    if o_data then
      log("debug", "%s sent private stanza to %s (%s)", from, to, o_data.jid);
      if stanza.name == "iq" then
        local id = stanza.attr.id;
        if stanza.attr.type == "get" or stanza.attr.type == "set" then
          stanza.attr.from, stanza.attr.to, stanza.attr.id = construct_stanza_id(SELF, stanza);
        else
          stanza.attr.from, stanza.attr.to, stanza.attr.id = deconstruct_stanza_id(SELF, stanza);
        end
        if type == 'get' and stanza.tags[1].attr.xmlns == 'vcard-temp' then
          stanza.attr.to = jid_bare(stanza.attr.to);
        end
        if stanza.attr.id then
          room_mt___route_stanza(SELF,stanza);
        end
        stanza.attr.from, stanza.attr.to, stanza.attr.id = from, to, id;
      else
        -- message
        stanza.attr.from = current_nick;
        for jid in pairs(o_data.sessions) do
          stanza.attr.to = jid;
          room_mt___route_stanza(SELF,stanza);
        end
        stanza.attr.from, stanza.attr.to = from, to;
      end
    elseif type ~= "error" and type ~= "result" then
      -- recipient not in room
      origin_send(origin, st.error_reply(stanza, "cancel", "item-not-found", "Recipient not in room"));
    end
  end
end


room_mt__send_form=function(SELF,origin, stanza)
  origin_send(origin, st.reply(stanza):query("http://jabber.org/protocol/muc#owner")
    :add_child(room_mt__get_form_layout(SELF):form())
  );
end


room_mt__get_form_layout=function(SELF)
  local form = dataform.new( {
      title = "Configuration for " .. SELF.jid,
      instructions = "Complete and submit this form to configure the room.",
      {
        name = 'FORM_TYPE',
        type = 'hidden',
        value = 'http://jabber.org/protocol/muc#roomconfig'
      },
      {
        name = 'muc#roomconfig_roomname',
        type = 'text-single',
        label = 'Name',
        value = room_mt__get_name(SELF) or "",
      },
      {
        name = 'muc#roomconfig_roomdesc',
        type = 'text-single',
        label = 'Description',
        value = room_mt__get_description(SELF) or "",
      },
      {
        name = 'muc#roomconfig_persistentroom',
        type = 'boolean',
        label = 'Make Room Persistent?',
        value = room_mt__is_persistent(SELF)
      },
      {
        name = 'muc#roomconfig_publicroom',
        type = 'boolean',
        label = 'Make Room Publicly Searchable?',
        value = not room_mt__is_hidden(SELF)
      },
      {
        name = 'muc#roomconfig_changesubject',
        type = 'boolean',
        label = 'Allow Occupants to Change Subject?',
        value = room_mt__get_changesubject(SELF)
      },
      {
        name = 'muc#roomconfig_whois',
        type = 'list-single',
        label = 'Who May Discover Real JIDs?',
        value =
        {
          { value = 'moderators', label = 'Moderators Only', default = SELF._data.whois == 'moderators' },
          { value = 'anyone', label = 'Anyone', default = SELF._data.whois == 'anyone' }
        }
      },
      {
        name = 'muc#roomconfig_roomsecret',
        type = 'text-private',
        label = 'Password',
        value = room_mt__get_password(SELF) or "",
      },
      {
        name = 'muc#roomconfig_moderatedroom',
        type = 'boolean',
        label = 'Make Room Moderated?',
        value = room_mt__is_moderated(SELF)
      },
      {
        name = 'muc#roomconfig_membersonly',
        type = 'boolean',
        label = 'Make Room Members-Only?',
        value = room_mt__is_members_only(SELF)
      },
      {
        name = 'muc#roomconfig_historylength',
        type = 'text-single',
        label = 'Maximum Number of History Messages Returned by Room',
        value = tostring(room_mt__get_historylength(SELF))
      }
      } );
  return --[[-- disabled module:fire_event("muc-config-form", { room = SELF, form = form }) or--]] form;
end
room_mt__process_form=function(SELF,origin, stanza)
  local query = stanza.tags[1];
  local form;
  for _, tag in ipairs(query.tags) do if tag.name == "x" and tag.attr.xmlns == "jabber:x:data" then form = tag; break; end end
  if not form then origin_send(origin, st.error_reply(stanza, "cancel", "service-unavailable")); return; end
  if form.attr.type == "cancel" then origin_send(origin, st.reply(stanza)); return; end
  if form.attr.type ~= "submit" then origin_send(origin, st.error_reply(stanza, "cancel", "bad-request", "Not a submitted form")); return; end

  local fields = room_mt__get_form_layout(SELF):data(form);
  if fields.FORM_TYPE ~= "http://jabber.org/protocol/muc#roomconfig" then origin_send(origin, st.error_reply(stanza, "cancel", "bad-request", "Form is not of type room configuration")); return; end

  local dirty = false

  local event = { room = SELF, fields = fields, changed = dirty };
  -- disabled module:fire_event("muc-config-submitted", event);
  dirty = event.changed or dirty;

  local name = fields['muc#roomconfig_roomname'];
  if name ~= room_mt__get_name(SELF) then
    room_mt__set_name(SELF,name);
  end

  local description = fields['muc#roomconfig_roomdesc'];
  if description ~= room_mt__get_description(SELF) then
    room_mt__set_description_ly(SELF,description);
  end

  local persistent = fields['muc#roomconfig_persistentroom'];
  dirty = dirty or(room_mt__is_persistent(SELF) ~= persistent)
  -- module:log("error", "persistent=%s", tostring(persistent));

  local moderated = fields['muc#roomconfig_moderatedroom'];
  dirty = dirty or(room_mt__is_moderated(SELF) ~= moderated)
  -- module:log("error", "moderated=%s", tostring(moderated));

  local membersonly = fields['muc#roomconfig_membersonly'];
  dirty = dirty or(room_mt__is_members_only(SELF) ~= membersonly)
  -- module:log("error", "membersonly=%s", tostring(membersonly));

  local public = fields['muc#roomconfig_publicroom'];
  dirty = dirty or(room_mt__is_hidden(SELF) ~=(not public and true or nil))

  local changesubject = fields['muc#roomconfig_changesubject'];
  dirty = dirty or(room_mt__get_changesubject(SELF) ~=(not changesubject and true or nil))
  -- module:log('error', 'changesubject=%s', changesubject and "true" or "false")

  local historylength = tonumber(fields['muc#roomconfig_historylength']);
  dirty = dirty or(historylength and(room_mt__get_historylength(SELF) ~= historylength));
  -- module:log('error', 'historylength=%s', historylength)


  local whois = fields['muc#roomconfig_whois'];
  if not valid_whois[whois] then
    origin_send(origin, st.error_reply(stanza, 'cancel', 'bad-request', "Invalid value for 'whois'"));
    return;
  end
  local whois_changed = SELF._data.whois ~= whois
  SELF._data.whois = whois
  -- module:log('error', 'whois=%s', whois)

  local password = fields['muc#roomconfig_roomsecret'];
  if room_mt__get_password(SELF) ~= password then
    room_mt__set_password(SELF,password);
  end
  room_mt__set_moderated(SELF,moderated);
  room_mt__set_members_only(SELF,membersonly);
  room_mt__set_persistent(SELF,persistent);
  room_mt__set_hidden(SELF,not public);
  room_mt__set_changesubject(SELF,changesubject);
  room_mt__set_historylength(SELF,historylength);

  room_save(SELF,true) --if SELF.save then SELF:save(true); end
  origin_send(origin, st.reply(stanza));

  if dirty or whois_changed then
    local msg = st.message( { type = 'groupchat', from = SELF.jid })
    :tag('x', { xmlns = 'http://jabber.org/protocol/muc#user' })

    if dirty then
      msg.tags[1]:tag('status', { code = '104' }):up();
    end
    if whois_changed then
      local code =(whois == 'moderators') and "173" or "172";
      msg.tags[1]:tag('status', { code = code }):up();
    end

    msg:up();

    room_mt__broadcast_message(SELF,msg, false)
  end
end
room_mt__destroy=function(SELF,newjid, reason, password)
  local pr = st.presence( { type = "unavailable" })
  :tag("x", { xmlns = "http://jabber.org/protocol/muc#user" })
  :tag("item", { affiliation = 'none', role = 'none' }):up()
  :tag("destroy", { jid = newjid })
  if reason then pr:tag("reason"):text(reason):up(); end
  if password then pr:tag("password"):text(password):up(); end
  for nick, occupant in pairs(SELF._occupants) do
    pr.attr.from = nick;
    for jid in pairs(occupant.sessions) do
      pr.attr.to = jid;
      room_mt___route_stanza(SELF,pr);
      SELF._jid_nick[jid] = nil;
    end
    SELF._occupants[nick] = nil;
  end
  room_mt__set_persistent(SELF,false);
  -- disabled module:fire_event("muc-room-destroyed", { room = SELF });
end

-- LY: This function is digested from room_mt__handle_to_room=function(SELF,origin, stanza)
room_mt__send_invitation=function(SELF, invitor,invitee, reason)
  local room_jid=SELF.jid

  local invite = st.message( { from = room_jid, to = invitee--[[, id = stanza.attr.id --]] })
  :tag('x', { xmlns = 'http://jabber.org/protocol/muc#user' })
  :tag('invite', { from = invitor })
  :tag('reason'):text(reason or ""):up()
  :up();
  if room_mt__get_password(SELF) then
    invite:tag("password"):text(room_mt__get_password(SELF)):up();
  end
  invite:up()
  :tag('x', { xmlns = "jabber:x:conference", jid = room_jid })
  -- COMPAT: Some older clients expect this
  :text(reason or "")
  :up()
  :tag('body')
  -- Add a plain message for clients which don't support invites
  :text(invitor .. ' invited you to the room ' .. room_jid ..(reason and(' (' .. reason .. ')') or ""))
  :up();
  if room_mt__is_members_only(SELF) and not room_mt__get_affiliation(SELF,invitee) then
    log("debug", "%s invited %s into members only room %s, granting membership", invitor, invitee, room_jid);
    room_mt__set_affiliation(SELF,invitor, invitee, "member", nil, "Invited by " .. SELF._jid_nick[invitor])
  end
  room_mt___route_stanza(SELF,invite);

  module:log("error", "%s invited %s into members only room %s, granting membership", invitor, invitee, room_jid);
end


room_mt__handle_to_room=function(SELF,origin, stanza)
  -- presence changes and groupchat messages, along with disco/etc
  local type = stanza.attr.type;
  local xmlns = stanza.tags[1] and stanza.tags[1].attr.xmlns;
  if stanza.name == "iq" then
    if xmlns == "http://jabber.org/protocol/disco#info" and type == "get" and not stanza.tags[1].attr.node then
      origin_send(origin, room_mt__get_disco_info(SELF,stanza));
    elseif xmlns == "http://jabber.org/protocol/disco#items" and type == "get" and not stanza.tags[1].attr.node then
      origin_send(origin, room_mt__get_disco_items(SELF,stanza));
    elseif xmlns == "http://jabber.org/protocol/muc#admin" then
      local actor = stanza.attr.from;
      local affiliation = room_mt__get_affiliation(SELF,actor);
      local current_nick = SELF._jid_nick[actor];
      local role = current_nick and SELF._occupants[current_nick].role or room_mt__get_default_role(SELF,affiliation);
      local item = stanza.tags[1].tags[1];
      if item and item.name == "item" then
        if type == "set" then
          local callback = function() origin_send(origin, st.reply(stanza)); end
          if item.attr.jid then
            -- Validate provided JID
            item.attr.jid = jid_prep(item.attr.jid);
            if not item.attr.jid then
              origin_send(origin, st.error_reply(stanza, "modify", "jid-malformed"));
              return;
            end
          end
          if not item.attr.jid and item.attr.nick then
            -- COMPAT Workaround for Miranda sending 'nick' instead of 'jid' when changing affiliation
            local occupant = SELF._occupants[SELF.jid .. "/" .. item.attr.nick];
            if occupant then item.attr.jid = occupant.jid; end
          elseif not item.attr.nick and item.attr.jid then
            local nick = SELF._jid_nick[item.attr.jid];
            if nick then item.attr.nick = select(3, jid_split(nick)); end
          end
          local reason = item.tags[1] and item.tags[1].name == "reason" and #item.tags[1] == 1 and item.tags[1][1];
          if item.attr.affiliation and item.attr.jid and not item.attr.role then
            local success, errtype, err = room_mt__set_affiliation(SELF,actor, item.attr.jid, item.attr.affiliation, callback, reason);
            if not success then origin_send(origin, st.error_reply(stanza, errtype, err)); end
          elseif item.attr.role and item.attr.nick and not item.attr.affiliation then
            local success, errtype, err = room_mt__set_role(SELF,actor, SELF.jid .. "/" .. item.attr.nick, item.attr.role, callback, reason);
            if not success then origin_send(origin, st.error_reply(stanza, errtype, err)); end
          else
            origin_send(origin, st.error_reply(stanza, "cancel", "bad-request"));
          end
        elseif type == "get" then
          local _aff = item.attr.affiliation;
          local _rol = item.attr.role;
          if _aff and not _rol then
            if affiliation == "owner" or(affiliation == "admin" and _aff ~= "owner" and _aff ~= "admin") then
              local reply = st.reply(stanza):query("http://jabber.org/protocol/muc#admin");
              for jid, affiliation in pairs(SELF._affiliations) do
                if affiliation == _aff then
                  reply:tag("item", { affiliation = _aff, jid = jid }):up();
                end
              end
              origin_send(origin, reply);
            else
              origin_send(origin, st.error_reply(stanza, "auth", "forbidden"));
            end
          elseif _rol and not _aff then
            if role == "moderator" then
              -- TODO allow admins and owners not in room? Provide read-only access to everyone who can see the participants anyway?
              if _rol == "none" then _rol = nil; end
              local reply = st.reply(stanza):query("http://jabber.org/protocol/muc#admin");
              for occupant_jid, occupant in pairs(SELF._occupants) do
                if occupant.role == _rol then
                  reply:tag("item", {
                      nick = select(3,jid_split(occupant_jid)),
                      role = _rol or "none",
                      affiliation = occupant.affiliation or "none",
                      jid = occupant.jid
                      } ):up();
                end
              end
              origin_send(origin, reply);
            else
              origin_send(origin, st.error_reply(stanza, "auth", "forbidden"));
            end
          else
            origin_send(origin, st.error_reply(stanza, "cancel", "bad-request"));
          end
        end
      elseif type == "set" or type == "get" then
        origin_send(origin, st.error_reply(stanza, "cancel", "bad-request"));
      end
    elseif xmlns == "http://jabber.org/protocol/muc#owner" and(type == "get" or type == "set") and stanza.tags[1].name == "query" then
      if room_mt__get_affiliation(SELF,stanza.attr.from) ~= "owner" then
        origin_send(origin, st.error_reply(stanza, "auth", "forbidden", "Only owners can configure rooms"));
      elseif stanza.attr.type == "get" then
        room_mt__send_form(SELF,origin, stanza);
      elseif stanza.attr.type == "set" then
        local child = stanza.tags[1].tags[1];
        if not child then
          origin_send(origin, st.error_reply(stanza, "modify", "bad-request"));
        elseif child.name == "destroy" then
          local newjid = child.attr.jid;
          local reason, password;
          for _, tag in ipairs(child.tags) do
            if tag.name == "reason" then
              reason = #tag.tags == 0 and tag[1];
            elseif tag.name == "password" then
              password = #tag.tags == 0 and tag[1];
            end
          end
          room_mt__destroy(SELF,newjid, reason, password);
          origin_send(origin, st.reply(stanza));
        else
          room_mt__process_form(SELF,origin, stanza);
        end
      end
    elseif type == "set" or type == "get" then
      origin_send(origin, st.error_reply(stanza, "cancel", "service-unavailable"));
    end
  elseif stanza.name == "message" and type == "groupchat" then
    local from, to = stanza.attr.from, stanza.attr.to;
    local current_nick = SELF._jid_nick[from];
    local occupant = SELF._occupants[current_nick];
    if not occupant then
      -- not in room
      origin_send(origin, st.error_reply(stanza, "cancel", "not-acceptable"));
    elseif occupant.role == "visitor" then
      origin_send(origin, st.error_reply(stanza, "auth", "forbidden"));
    else
      local from = stanza.attr.from;
      stanza.attr.from = current_nick;
      local subject = getText(stanza, { "subject" });
      if subject then
        if occupant.role == "moderator" or
        (SELF._data.changesubject and occupant.role == "participant") then
          -- and participant
          room_mt__set_subject(SELF,current_nick, subject);
          -- TODO use broadcast_message_stanza
        else
          stanza.attr.from = from;
          origin_send(origin, st.error_reply(stanza, "auth", "forbidden"));
        end
      else
        room_mt__broadcast_message(SELF,stanza, room_mt__get_historylength(SELF) > 0 and stanza:get_child("body"));
      end
      stanza.attr.from = from;
    end
  elseif stanza.name == "message" and type == "error" and is_kickable_error(stanza) then
    local current_nick = SELF._jid_nick[stanza.attr.from];
    log("debug", "%s kicked from %s for sending an error message", current_nick, SELF.jid);
    room_mt__handle_to_occupant(SELF,origin, build_unavailable_presence_from_error(stanza));
    -- send unavailable
  elseif stanza.name == "presence" then
    -- hack - some buggy clients send presence updates to the room rather than their nick
    local to = stanza.attr.to;
    local current_nick = SELF._jid_nick[stanza.attr.from];
    if current_nick then
      stanza.attr.to = current_nick;
      room_mt__handle_to_occupant(SELF,origin, stanza);
      stanza.attr.to = to;
    elseif type ~= "error" and type ~= "result" then
      origin_send(origin, st.error_reply(stanza, "cancel", "service-unavailable"));
    end
  elseif stanza.name == "message" and not(type == "chat" or type == "error" or type == "groupchat" or type == "headline") and #stanza.tags == 1
  and SELF._jid_nick[stanza.attr.from] and stanza.tags[1].name == "x" and stanza.tags[1].attr.xmlns == "http://jabber.org/protocol/muc#user" then
    local x = stanza.tags[1];
    local payload =(#x.tags == 1 and x.tags[1]);
    if payload and payload.name == "invite" and payload.attr.to then
      local _from, _to = stanza.attr.from, stanza.attr.to;
      local _invitee = jid_prep(payload.attr.to);
      if _invitee then
        local _reason = payload.tags[1] and payload.tags[1].name == 'reason' and #payload.tags[1].tags == 0 and payload.tags[1][1];
        local invite = st.message( { from = _to, to = _invitee, id = stanza.attr.id })
        :tag('x', { xmlns = 'http://jabber.org/protocol/muc#user' })
        :tag('invite', { from = _from })
        :tag('reason'):text(_reason or ""):up()
        :up();
        if room_mt__get_password(SELF) then
          invite:tag("password"):text(room_mt__get_password(SELF)):up();
        end
        invite:up()
        :tag('x', { xmlns = "jabber:x:conference", jid = _to })
        -- COMPAT: Some older clients expect this
        :text(_reason or "")
        :up()
        :tag('body')
        -- Add a plain message for clients which don't support invites
        :text(_from .. ' invited you to the room ' .. _to ..(_reason and(' (' .. _reason .. ')') or ""))
        :up();
        if room_mt__is_members_only(SELF) and not room_mt__get_affiliation(SELF,_invitee) then
          log("debug", "%s invited %s into members only room %s, granting membership", _from, _invitee, _to);
          room_mt__set_affiliation(SELF,_from, _invitee, "member", nil, "Invited by " .. SELF._jid_nick[_from])
        end
        room_mt___route_stanza(SELF,invite);
      else
        origin_send(origin, st.error_reply(stanza, "cancel", "jid-malformed"));
      end
    else
      origin_send(origin, st.error_reply(stanza, "cancel", "bad-request"));
    end
  else
    if type == "error" or type == "result" then return; end
    origin_send(origin, st.error_reply(stanza, "cancel", "service-unavailable"));
  end
end


room_mt__handle_stanza=function(SELF,origin, stanza)
  local to_node, to_host, to_resource = jid_split(stanza.attr.to);
  if to_resource then
    room_mt__handle_to_occupant(SELF,origin, stanza);
  else
    room_mt__handle_to_room(SELF,origin, stanza);
  end
end

--[[
-- Due to de-OOP, we don't need this fallback declare any more
room_mt__route_stanza=function(SELF,stanza) end -- Replace with a routing function, e.g., function(room, stanza) core_route_stanza(origin, stanza); end
--]]
-- LY: I should call this function instead access fields directly

room_mt__get_affiliation=function(SELF,jid)
  if is_admin(jid) then return "owner"; end
  -- LY: Combined from original mod_muc.lua

  local node, host, resource = jid_split(jid);
  local bare = node and node .. "@" .. host or host;
  local result = SELF._affiliations[bare];
  -- Affiliations are granted, revoked, and maintained based on the user's bare JID.
  if not result and SELF._affiliations[host] == "outcast" then result = "outcast"; end
  -- host banned
  return result;
end
-- LY: I should call this function instead access fields directly

room_mt__set_affiliation=function(SELF,actor, jid, affiliation, callback, reason)
  if affiliation ~= "owner" and is_admin(jid) then return nil, "modify", "not-acceptable"; end
  -- LY: Combined from original mod_muc.lua

  jid = jid_bare(jid);
  if affiliation == "none" then affiliation = nil; end
  if affiliation and affiliation ~= "outcast" and affiliation ~= "owner" and affiliation ~= "admin" and affiliation ~= "member" then
    return nil, "modify", "not-acceptable";
  end
  if actor ~= true then
    local actor_affiliation = room_mt__get_affiliation(SELF,actor);
    local target_affiliation = room_mt__get_affiliation(SELF,jid);
    if target_affiliation == affiliation then
      -- no change, shortcut
      if callback then callback(); end
      return true;
    end
    if actor_affiliation ~= "owner" then
      if affiliation == "owner" or affiliation == "admin" or actor_affiliation ~= "admin" or target_affiliation == "owner" or target_affiliation == "admin" then
        return nil, "cancel", "not-allowed";
      end
    elseif target_affiliation == "owner" and jid_bare(actor) == jid then
      -- SELF change
      local is_last = true;
      for j, aff in pairs(SELF._affiliations) do if j ~= jid and aff == "owner" then is_last = false; break; end end
      if is_last then
        return nil, "cancel", "conflict";
      end
    end
  end
  SELF._affiliations[jid] = affiliation;
  local role = room_mt__get_default_role(SELF,affiliation);
  local x = st.stanza("x", { xmlns = "http://jabber.org/protocol/muc#user" })
  :tag("item", { affiliation = affiliation or "none", role = role or "none" })
  :tag("reason"):text(reason or ""):up()
  :up();
  local presence_type = nil;
  if not role then
    -- getting kicked
    presence_type = "unavailable";
    if affiliation == "outcast" then
      x:tag("status", { code = "301" }):up();
      -- banned
    else
      x:tag("status", { code = "321" }):up();
      -- affiliation change
    end
  end
  local modified_nicks = { };
  for nick, occupant in pairs(SELF._occupants) do
    if jid_bare(occupant.jid) == jid then
      if not role then
        -- getting kicked
        SELF._occupants[nick] = nil;
      else
        occupant.affiliation, occupant.role = affiliation, role;
      end
      for jid, pres in pairs(occupant.sessions) do
        -- remove for all sessions of the nick
        if not role then SELF._jid_nick[jid] = nil; end
        local p = st.clone(pres);
        p.attr.from = nick;
        p.attr.type = presence_type;
        p.attr.to = jid;
        p:add_child(x);
        room_mt___route_stanza(SELF,p);
        if occupant.jid == jid then
          modified_nicks[nick] = p;
        end
      end
    end
  end
  room_save(SELF) --if SELF.save then SELF:save(); end
  if callback then callback(); end
  for nick, p in pairs(modified_nicks) do
    p.attr.from = nick;
    room_mt__broadcast_except_nick_ly(SELF,p, nick);
  end
  return true;
end


room_mt__get_role=function(SELF,nick)
  local session = SELF._occupants[nick];
  return session and session.role or nil;
end

room_mt__can_set_role=function(SELF,actor_jid, occupant_jid, role)
  local occupant = SELF._occupants[occupant_jid];
  if not occupant or not actor_jid then return nil, "modify", "not-acceptable"; end

  if actor_jid == true then return true; end

  local actor = SELF._occupants[SELF._jid_nick[actor_jid]];
  if actor and actor.role == "moderator" then
    if occupant.affiliation ~= "owner" and occupant.affiliation ~= "admin" then
      if actor.affiliation == "owner" or actor.affiliation == "admin" then
        return true;
      elseif occupant.role ~= "moderator" and role ~= "moderator" then
        return true;
      end
    end
  end
  return nil, "cancel", "not-allowed";
end

room_mt__set_role=function(SELF,actor, occupant_jid, role, callback, reason)
  if role == "none" then role = nil; end
  if role and role ~= "moderator" and role ~= "participant" and role ~= "visitor" then return nil, "modify", "not-acceptable"; end
  local allowed, err_type, err_condition = room_mt__can_set_role(SELF,actor, occupant_jid, role);
  if not allowed then return allowed, err_type, err_condition; end
  local occupant = SELF._occupants[occupant_jid];
  local x = st.stanza("x", { xmlns = "http://jabber.org/protocol/muc#user" })
  :tag("item", { affiliation = occupant.affiliation or "none", nick = select(3, jid_split(occupant_jid)), role = role or "none" })
  :tag("reason"):text(reason or ""):up()
  :up();
  local presence_type = nil;
  if not role then
    -- kick
    presence_type = "unavailable";
    SELF._occupants[occupant_jid] = nil;
    for jid in pairs(occupant.sessions) do
      -- remove for all sessions of the nick
      SELF._jid_nick[jid] = nil;
    end
    x:tag("status", { code = "307" }):up();
  else
    occupant.role = role;
  end
  local bp;
  for jid, pres in pairs(occupant.sessions) do
    -- send to all sessions of the nick
    local p = st.clone(pres);
    p.attr.from = occupant_jid;
    p.attr.type = presence_type;
    p.attr.to = jid;
    p:add_child(x);
    room_mt___route_stanza(SELF,p);
    if occupant.jid == jid then
      bp = p;
    end
  end
  if callback then callback(); end
  if bp then
    room_mt__broadcast_except_nick_ly(SELF,bp, occupant_jid);
  end
  return true;
end


room_mt___route_stanza=function(SELF,stanza)
  local muc_child;
  local to_occupant = SELF._occupants[SELF._jid_nick[stanza.attr.to]];
  local from_occupant = SELF._occupants[stanza.attr.from];
  if stanza.name == "presence" then
    if to_occupant and from_occupant then
      if SELF._data.whois == 'anyone' then
        muc_child = stanza:get_child("x", "http://jabber.org/protocol/muc#user");
      else
        if to_occupant.role == "moderator" or jid_bare(to_occupant.jid) == jid_bare(from_occupant.jid) then
          muc_child = stanza:get_child("x", "http://jabber.org/protocol/muc#user");
        end
      end
    end
  end
  if muc_child then
    for _, item in pairs(muc_child.tags) do
      if item.name == "item" then
        if from_occupant == to_occupant then
          item.attr.jid = stanza.attr.to;
        else
          item.attr.jid = from_occupant.jid;
        end
      end
    end
  end
  -- The original code is: self:route_stanza(stanza);
  room_route_stanza(SELF, stanza);--SELF:route_stanza(stanza);  --LY: we still use the original format, but with SELF instead of self.

  if muc_child then
    for _, item in pairs(muc_child.tags) do
      if item.name == "item" then
        item.attr.jid = nil;
      end
    end
  end
end

-- local _M = {}; -- module "muc" LY: Disabled due to combining
-- local a={}---- a="" -- a for abbreviation name, which is a short name for members for instance room. Or maybe a short JID for a JID of an instance room. Later we will implement this

--local function --[[_M.  LY: Disabled due to combining--]]new_room(jid, config)  -- LY: This is the key to create a room

--local function --[[_M.  LY: Disabled due to combining--]]set_max_history_length(_max_history_length)
set_max_history_length=function(_max_history_length)
  max_history_length = _max_history_length or math.huge;
end

--_M.room_mt = room_mt; LY: Disabled due to combining

--return _M;-- LY: Disabled due to combining




--[[ ************************ combined to the original class method of set_affiliation, get_affiliation.
local _set_affiliation = muc_new_room.room_mt.set_affiliation;
local _get_affiliation = muc_new_room.room_mt.get_affiliation;
local function muclib.room_mt__get_affiliation(SELF,jid)
	if is_admin(jid) then return "owner"; end
	return _get_affiliation(SELF, jid);
end
local function muclib.room_mt__set_affiliation(SELF,actor, jid, affiliation, callback, reason)
	if affiliation ~= "owner" and is_admin(jid) then return nil, "modify", "not-acceptable"; end
	return _set_affiliation(SELF, actor, jid, affiliation, callback, reason);
end
--- ************************ End combined to the original class method of set_affiliation, get_affiliation.--]]



Create_Persistent_Room=function()
-- LY: To create rooms for persistent_rooms
  local persistent_errors = false;
  for jid in pairs(persistent_rooms) do
    local node = jid_split(jid);
    local data = room_configs:get(node);
    if data then
      local room = create_room(jid);  -- LY: so persisent_rooms are created as room.
      room._data = data._data;
      room._affiliations = data._affiliations;
    else -- missing room data
      persistent_rooms[jid] = nil;
      -- module:log("error", "Missing data for room '%s', removing from persistent room list", jid);
      persistent_errors = true;
    end
  end
  if persistent_errors then persistent_rooms_storage:set(nil, persistent_rooms); end
end

get_disco_info=function(stanza)   --LY: we still use 'conference' as category just in case some incompliant
  return st.iq({type='result', id=stanza.attr.id, from=muc_host, to=stanza.attr.from}):query("http://jabber.org/protocol/disco#info")
  :tag("identity", {category='conference', type='text', name=muc_name}):up()  
  :tag("feature", {var="http://jabber.org/protocol/muc"}); -- TODO cache disco reply
end

get_disco_items=function(stanza)
  local reply = st.iq({type='result', id=stanza.attr.id, from=muc_host, to=stanza.attr.from}):query("http://jabber.org/protocol/disco#items");
  for jid, room in pairs(rooms) do
    if not room_mt__is_hidden(room) then
      reply:tag("item", {jid=jid, name=room_mt__get_name(room)}):up();
    end
  end
  return reply; -- TODO cache disco reply
end

--LY: to handle non roomt event, so far no need to modify, but we need to think about it again later

handle_to_domain=function(event)
  local origin, stanza = event.origin, event.stanza;
  local type = stanza.attr.type;
  if type == "error" or type == "result" then return; end
  if stanza.name == "iq" and type == "get" then
    local xmlns = stanza.tags[1].attr.xmlns;
    local node = stanza.tags[1].attr.node;
    if xmlns == "http://jabber.org/protocol/disco#info" and not node then
      origin_send(origin,get_disco_info(stanza)); 
    elseif xmlns == "http://jabber.org/protocol/disco#items" and not node then
      origin_send(origin,get_disco_items(stanza)); 
    elseif xmlns == "http://jabber.org/protocol/muc#unique" then
      origin_send(origin,st.reply(stanza):tag("unique", {xmlns = xmlns}):text(uuid_gen())); -- FIXME Random UUIDs can theoretically have collisions

    else
      origin_send(origin,st.error_reply(stanza, "cancel", "service-unavailable")); -- TODO disco/etc  
    end
  else
    room_mt__handle_stanza(host_room,origin, stanza);
    --origin_send(origin,st.error_reply(stanza, "cancel", "service-unavailable", "The muc server doesn't deal with messages and presence directed at it"));
  end
  return true;
end



shutdown_room=function(room, stanza)
  for nick, occupant in pairs(room._occupants) do
    stanza.attr.from = nick;
    for jid in pairs(occupant.sessions) do
      stanza.attr.to = jid;
      room_mt___route_stanza(room,stanza);
      room._jid_nick[jid] = nil;
    end
    room._occupants[nick] = nil;
  end
end

shutdown_component=function()
  if not saved then
    local stanza = st.presence({type = "unavailable"})
    :tag("x", {xmlns = "http://jabber.org/protocol/muc#user"})
    :tag("item", { affiliation='none', role='none' }):up();
    for roomjid, room in pairs(rooms) do
      shutdown_room(room, stanza);
    end
    shutdown_room(host_room, stanza);
  end
end

InitModule=function()
--*******************************************************************************************************************
-- Init part 
--*******************************************************************************************************************
  if module:get_host_type() ~= "component" then
    error("Role should be loaded as a component, please see http://prosody.im/doc/components", 0);
  end

-- Configurable options
--[[muclib.  LY: Disabled due to combining--]]set_max_history_length(module:get_option_number("max_history_messages"));

  host_room = muc_new_room(muc_host);

  Create_Persistent_Room()

  module:hook("iq/bare", stanza_handler_ly, -1);
  module:hook("message/bare", stanza_handler_ly, -1);
  module:hook("presence/bare", stanza_handler_ly, -1);
  module:hook("iq/full", stanza_handler_ly, -1);
  module:hook("message/full", stanza_handler_ly, -1);
  module:hook("presence/full", stanza_handler_ly, -1);
  module:hook("iq/host", handle_to_domain, -1);
  module:hook("message/host", handle_to_domain, -1);
  module:hook("presence/host", handle_to_domain, -1);

  hosts[module.host].send = function(stanza) -- FIXME do a generic fix
    if stanza.attr.type == "result" or stanza.attr.type == "error" then
      module_send(stanza);  
    else error("component.send only supports result and error stanzas at the moment"); end
  end

  hosts[module:get_host()].muc = { rooms = rooms };

  module.save = function()
    saved = true;
    return {rooms = rooms};
  end
  module.restore = function(data)
    for jid, oldroom in pairs(data.rooms or {}) do
      local room = create_room(jid);
      room._jid_nick = oldroom._jid_nick;
      room._occupants = oldroom._occupants;
      room._data = oldroom._data;
      room._affiliations = oldroom._affiliations;
    end
    hosts[module:get_host()].muc = { rooms = rooms };
  end

  module.unload = shutdown_component;
  module:hook_global("server-stopping", shutdown_component);

  module:log("info", "Role Chat component. Copyright 2016 Ying LI (Mr.Ying.Lee@Gmail.com) All rights reserved. This component is made possible by Prosody open source project, created by Matthew Wild and Waqas Hussain.");
end 

InitModule()  --LY: this must be the last statement