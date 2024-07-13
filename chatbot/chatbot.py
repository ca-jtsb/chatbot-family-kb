from pyswip import Prolog
import re

prolog = Prolog()
prolog.consult("knowledgebase.pl")  # consults the knowledge base

#declare array consisting unique non-name english words
NON_NAME_WORDS = ["who", "and", "are", "is", "a", "an", "the", "of"]
RELATION_WORDS = ["parent", "parents", "father", "fathers",
                  "mother", "mothers", "child", "children",
                  "son", "sons", "daughter", "daughters",
                  "sibling", "siblings", "sister", "sisters",
                  "brother", "brothers", "uncle", "uncles",
                  "aunt", "aunts", "relative", "relatives",
                  "grandfather", "grandfathers", "grandmother", "grandmothers"]

def get_relation(sentence):
    words = sentence.lower().split()
    #print(words)
    for i in range(len(words)):
        words[i] = words[i].translate({ord('?'): None, ord(','): None, ord('.'): None})
    #print(words)
    if 'parent' in words or 'parents' in words:         return 'parent'

    elif 'grandfather' in words or 'grandfathers' in words: return 'grandfather'
    elif 'grandmother' in words or 'grandmothers' in words: return 'grandmother'

    elif 'father' in words or 'fathers' in words:       return 'father'
    elif 'mother' in words or 'mothers' in words:       return 'mother'

    elif 'child' in words or 'children' in words:       return 'child'
    elif 'son' in words or 'sons' in words:             return 'son' 
    elif 'daughter' in words or 'daughters' in words:   return 'daughter'

    elif 'sibling' in words or 'siblings' in words:     return 'sibling'
    elif 'sister' in words or 'sisters' in words:       return 'sister'
    elif 'brother' in words or 'brothers' in words:     return 'brother'

    elif 'uncle' in words or 'uncles' in words:         return 'uncle'
    elif 'aunt' in words or 'aunts' in words:           return 'aunt'
    elif 'relative' in words or 'relatives' in words:   return 'relative'

    return None

# parses the sentence to get all names
def parse_names(words, relation):
    names = []

    # ignores NON_NAME_WORDS and RELATION words
    for word in words:
        # removes '?", ',' and '.' from names
        word = word.translate({ord('?'): None, ord(','): None, ord('.'): None})
        if not any(word == rel_word or f" {rel_word} " in f" {word} " for rel_word in RELATION_WORDS) and word not in NON_NAME_WORDS:
            names.append(word)
    
    # if there is at least one unique name
    #print(f"{len(names)} names")

    if (len(names) > 0):
        names_1 = []
        for i in range(len(names)-1):
            names_1.append(names[i])    # gets the list of names before the last name
 
        name_2 = names[len(names)-1]  # the single last name in the list is usually the Y variable in an (X, Y) query
        return names_1, name_2
    else:
        return None, None

def process_question(question_word, relation, words):
    # parse the names from the question first
    names_1, name_2 = parse_names(words, relation)

    if (names_1 == None and name_2 == None):
        print("No name found!")
        return

    #print(names_1)
    #print(name_2)
    if (question_word == 'who'):
        name = words[len(words)-1].translate({ord('?'): None}) # who questions always have names at end

        name_list = list(prolog.query(f"{relation}(X, {name})"))
        # if list yields at least 1 result, prints out in appropriate format
        if (len(name_list) >= 1):
            name_set = set(val for  dic in name_list for val in dic.values())
            for x in name_set:
                print(x.capitalize())
        # else prints notice
        else:
            print(f"No {relation} found!")
    elif(question_word == 'is'):
        name = words[1].translate({ord('?'): None})  
        name_2 = words[len(words)-1].translate({ord('?'): None})  
        result = bool(list(prolog.query(f"{relation}({name}, {name_2})")))  
        if (result == True):
            print("Yes!")
        else:
            print("No!")

    elif(question_word == 'are'):
        for name in names_1:
            result = True
            check = bool(list(prolog.query(f"{relation}({name}, {name_2})")))
            if (check != True):
                result = False  # once it encounters a false relationship, becomes false
                break
        if (result == True):
            print("Yes!")
        else:
            print("No!")
    else:
        print("Invalid sentence format, Please enter input again!\n")


def process_statement(relation, words):
    result = []
    names_1, name_2 = parse_names(words, relation)

    if (names_1 == None and name_2 == None):
        print("No name found!")
        return

    #print(names_1)
    #print(name_2)
    result = True # result of overall queries
    failed_queries = [0] * len(names_1)

    for i in range(len(names_1)):
        check = bool(list(prolog.query(f"{relation}({names_1[i]}, {name_2})")))
        # once it encounters a relationship that does not exist.
        if (check != True):
            result = False
            failed_queries[i] = -1 # failed queries will have a value of -1
            
    # handle entailment, contingency and contradiction

    # if result is true, entailment.
    if (result == True):
        print("I already know that!")
    # if result is false, contingency or contradiction.
    else:
        if (result == False):
            contradiction = False
            success = False

            if (relation == "parent"):
                for i in range(len(failed_queries)):
                    if (failed_queries[i] == -1):
                        add_result = bool(list(prolog.query(f"check_parent({names_1[i]}, {name_2})"))) # see if the query failed because it doesnt exist or it's simply impossible to add
                                                            
                        if (add_result):
                            success = True 
                        else:
                            success = False # if at least 1 impossible relationship, deems the whole statement a contradictions
                            break

                if (success):
                    for i in range(0, len(failed_queries)):
                        if (failed_queries[i] == -1):
                            #print(f"adding {names_1[i]}")
                            Prolog.assertz(f"parent({names_1[i]}, {name_2})") 
                            Prolog.assertz(f"ancestor({names_1[i]}, {name_2})")
                            Prolog.assertz(f"child({name_2}, {names_1[i]})")

            elif (relation == "mother"):
                success = bool(list(prolog.query(f"check_mother({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"parent({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"ancestor({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"child({name_2}, {names_1[0]})") 
                    Prolog.assertz(f"mother({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"female({names_1[0]})") 

            elif (relation == "father"):
                success = bool(list(prolog.query(f"check_father({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"parent({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"ancestor({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"child({name_2}, {names_1[0]})") 
                    Prolog.assertz(f"father({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"male({names_1[0]})")

            elif (relation == "child"):
                for i in range(len(failed_queries)):
                    if (failed_queries[i] == -1):
                        add_result = bool(list(prolog.query(f"check_child({names_1[i]}, {name_2})"))) # see if the query failed because it doesnt exist or it's simply impossible to add
                        #print(add_result)

                        if (add_result):
                            success = True 
                        else:
                            success = False
                            break

                if (success):
                    for i in range(len(failed_queries)):
                        if (failed_queries[i] == -1):
                            #print(f"adding {names_1[i]}")
                            Prolog.assertz(f"child({names_1[i]}, {name_2})")
                            Prolog.assertz(f"ancestor( {name_2}, {names_1[i]})") 
                            Prolog.assertz(f"parent({name_2},{names_1[i]})")
                            
            elif (relation == "son"):
                success = bool(list(prolog.query(f"check_son({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"parent({name_2}, {names_1[0]})")
                    Prolog.assertz(f"ancestor({name_2}, {names_1[0]})") 
                    Prolog.assertz(f"child({names_1[0]}, {name_2})")
                    Prolog.assertz(f"son({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"male({names_1[0]})") 

            elif (relation == "daughter"):
                success = bool(list(prolog.query(f"check_daughter({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"parent({name_2}, {names_1[0]})") 
                    Prolog.assertz(f"ancestor({name_2}, {names_1[0]})") 
                    Prolog.assertz(f"child({names_1[0]}, {name_2})") 
                    Prolog.assertz(f"daughter({names_1[0]}, {name_2})")
                    Prolog.assertz(f"female({names_1[0]})") 

            elif (relation == "sibling"):
                success = bool(list(prolog.query(f"check_sibling({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    #print(f"adding {names_1[0]} and {name_2} as siblings.")
                    #print("note: parents of new sibling won't be recognized until it's fed the new info. (half siblings can occur)")
                    Prolog.assertz(f"sibling({names_1[0]}, {name_2})")
                    Prolog.assertz(f"sibling({name_2}, {names_1[0]})")

            elif (relation == "sister"):
                success = bool(list(prolog.query(f"check_sister({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"sibling({names_1[0]}, {name_2})")
                    Prolog.assertz(f"sister({names_1[0]}, {name_2})")
                    Prolog.assertz(f"female({names_1[0]})")

            elif (relation == "brother"):
                success = bool(list(prolog.query(f"check_brother({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"sibling({names_1[0]}, {name_2})")
                    Prolog.assertz(f"brother({names_1[0]}, {name_2})")
                    Prolog.assertz(f"male({names_1[0]})")
            
            elif (relation == "aunt"):
                success = bool(list(prolog.query(f"check_aunt({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"aunt({names_1[0]}, {name_2})")
                    Prolog.assertz(f"ancestor({names_1[0]}, {name_2})")
                    Prolog.assertz(f"female({names_1[0]})") 
            
            elif (relation == "uncle"):
                success = bool(list(prolog.query(f"check_uncle({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"uncle({names_1[0]}, {name_2})")
                    Prolog.assertz(f"ancestor({names_1[0]}, {name_2})")
                    Prolog.assertz(f"male({names_1[0]})")

            elif (relation == "grandfather"):
                success = bool(list(prolog.query(f"check_grandfather({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"grandparent({names_1[0]}, {name_2})")
                    Prolog.assertz(f"grandfather({names_1[0]}, {name_2})")
                    Prolog.assertz(f"male({names_1[0]})")

            elif (relation == "grandmother"):
                success = bool(list(prolog.query(f"check_grandmother({names_1[0]}, {name_2})")))
                #print(success)
                if (success):
                    Prolog.assertz(f"grandparent({names_1[0]}, {name_2})")
                    Prolog.assertz(f"grandmother({names_1[0]}, {name_2})")
                    Prolog.assertz(f"female({names_1[0]})")
            
        if (success == False):
            print("That's impossible!")
        elif(success == True):
            print("OK! I learned something.")
    

# MAIN MENU LOOP

print("Welcome to the family friendly Chatbot!")
print("Ask the bot or tell the bot what it doesn't know about the family!\n")

while True:    
    sentence = str(input("Ask or tell the bot something! Otherwise, say 'bye' to exit:\n >>> ")).lower()
    relation = get_relation(sentence)

    #print(f"relation = {relation}") #testing

    # if user chooses to exit
    if("bye" in sentence):
        print("See you next time!\n")
        break
    # if user inputs a non-existing relation
    elif(relation == None):
        print("Invalid sentence format, Please enter input again!\n")
    # if user inputs a question
    elif ("?" in sentence):
        # use regex to match the sentence formats similar to statements below.
        match_result = re.search(r"^\b(are)\s([A-Za-z]+)\s(and)\s([A-Za-z]+)\s(siblings|relatives)\b\?$", sentence) # are _ and _ siblings/relatives?
        match_result_2 = re.search(r"^\b(are)\s([A-Za-z]+)\s(and)\s([A-Za-z]+)\s(the)\s(parents)\s(of)\s([A-Za-z]+)\b\?$", sentence) # are _ and _ the parents of _?
        match_result_3 = re.search(r"^\b(are)\s([A-Za-z]+)(,\s[A-Za-z]+)*\s(and)\s\b([A-Za-z]+)\s(children)\s(of)\s([A-Za-z]+)\b\?$", sentence) # are _, _, and _ children of _?
        match_result_4 = re.search(r"^\b(is)\s([A-Za-z]+)\s(a|an|the)\s({})\s(of)\s([A-Za-z]+)\b\?$".format(relation), sentence) # is _ a {relation} of _?
        match_result_5 = re.search(r"^\b(who)\s(is|are)\s(a|an|the)\s({}|parents|mothers|fathers|siblings|brothers|sisters|children|sons|daughters|relatives)\s(of)\s([A-Za-z]+)\?$".format(relation), sentence) # who is/are the {relation} of _?
        
        # split the sentence
        if ((match_result or match_result_2 or match_result_3 or match_result_4 or match_result_5)):
            words = list(sentence.split(" "))
            question_word = words[0]
            process_question(question_word, relation, words)
            print("")
        else:
            print("Invalid sentence format, Please enter input again!\n")
        
    # if user inputs a statement
    elif("." in sentence):
        match_result = re.search(r"^\b([A-Za-z]+)\s(is)\s(a|the|an)\s({})\s(of)\s\b([A-Za-z]+)\b\.$".format(relation), sentence) # _ is a/an/the {relation} of _.
        match_result_2 = re.search(r"^\b([A-Za-z]+)\s(and)\s\b([A-Za-z]+)\s(are)\s(siblings)\b\.$", sentence) # _ and _ are siblings.
        match_result_3 = re.search(r"^\b([A-Za-z]+)\s(and)\s\b([A-Za-z]+)\s(are)\s(the)\s(parents)\s(of)\s\b([A-Za-z]+)\b\.$", sentence) # _ and _ are the parents of _.
        match_result_4 = re.search(r"^\b([A-Za-z]+)(,\s[A-Za-z]+)*\s(and)\s\b([A-Za-z]+)\s(are)\s(children)\s(of)\s\b([A-Za-z]+)\b\.$", sentence) # _, _ and _ are children of _.
        
        if ((match_result or match_result_2 or match_result_3 or match_result_4)):
            words = list(sentence.split(" "))
            process_statement(relation, words)
            print("")
        else:
            print("Invalid sentence format, Please enter input again!\n")

    else:
        print("Invalid sentence format, Please enter input again!\n")
