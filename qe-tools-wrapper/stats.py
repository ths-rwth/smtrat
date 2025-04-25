class Statistics:
    def __init__(self):
        self.output_amount_or = 0
        self.output_amount_and = 0
        self.output_amount_atoms = 0

    def __str__(self):
        return '''(:output (
    :amout_or ''' + str(self.output_amount_or)  + '''
    :amount_and ''' + str(self.output_amount_and)  + '''
    :amount_atoms ''' + str(self.output_amount_atoms)  + '''
))'''