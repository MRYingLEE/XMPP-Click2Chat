User Role, such as Sales, Support, HR. It is different from the role in XMPP, say, None/Visitor/Participant/Moderator.


#Concept:
User Role is a template MUC to members of the role, and a restricted MUC (Only 1 other can join to protect privacy) for others. People always “groupchat” but not “chat” with user role. 

To implement “chat” interface with User Role is not good for we will miss some features of MUC, such as topic. If we extends, the XMPP client is not general (Commercially it is not bad). So make a compromise, we “groupchat” instead of “chat” with a role. At least there is a good excuse that 2 members of a role could join the discussion. (Let me rethink after I finish step 1).

#Step 1:
At first internally, a User Role is defined as a MUC, template MUC, such as  Sales@Role.Hotline.Chat
Persistent
Member Only.
Memberlist: The real person to play this role;
Admin:  The real person in charge to response?
Owner: IT or role leader
Allow Subject change by anyone. (For our scenario)
The description can be an XML based settings
Real Description
Persistent generated MUC?
Allow Anonymous access?
Allow external access?
ChatBot define?
Initial welcome statements
Predefined nicks. So that it is easy to join the MUC. Maybe we just use nick of this room.

##MUC creating
When a user (instead of a member)  wants to join the template MUC,  
If there is one already, return it; But for anonymous access, support history is not give back just in case privacy leaks.
If not,  internally I create a temporary MUC
Based on template MUC, we copy settings, 
The name is the name of the Template MUC+”---”+ that of visitor.
Such as Sales---88888888888888888888888@Role.Hotline.Chat; (So far local accounts only)

##Information flow
All flows from the visitor will be routed to the normal MUC;
All flows to the visitor will be faked as a normal chat in the name of MUC.
To the role members, all this is a normal MUC.
Invitation to role will be transferred to a MUC message; (Not needed so far)

##Routing
When the following things happened, the temp MUC will notify the template one:
The visitor sends the 1st message (This is the right time to remind members to join), just in case visitor doesn’t say anything. Later maybe improve.
The visitor leaves (This is the right time to remind to close the chat)
A member joins (This is the right time to remind other members)
A member leaves but the visitor is still in the MUC.
And every reminding, the system will list all not responding MUC in order for members to response.

In short, in the view of visitor, this is a private chat, in the view of members, this is a MUC. Both sides can use standard XMPP tools to discuss.

I need to check the logic of Support Chat.

#Step 2 (In future, long time later) : User Role based XMPP. To build User Role as a cornerstone concept in XMPP. This is beyond our requirement. So in foreseen future, we won’t do this.
